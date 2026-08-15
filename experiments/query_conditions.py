"""Conditioning diagnostics for Proposition 3.

The full weighted Laplacian is analyzed on the balanced subspace. Cases outside
the positive series susceptance model are returned as unavailable; branches are
never deleted or sign corrected to force the model to apply.
"""

from __future__ import annotations

from dataclasses import dataclass
import math

import networkx as nx
import numpy as np
from scipy import linalg, sparse
from scipy.sparse import linalg as sparse_linalg


EFFECTIVE_EPSILONS = (0.001, 0.01, 0.1)
PRIMARY_RATIO = 0.5
NUMERICAL_MARGIN = 1e-7


def weighted_laplacian(
    n: int, weights: dict[tuple[int, int], float]
) -> sparse.csr_matrix:
    """Build the positive weighted simple graph Laplacian."""
    rows: list[int] = []
    columns: list[int] = []
    values: list[float] = []
    diagonal = np.zeros(n)
    for (u, v), weight in weights.items():
        if not math.isfinite(weight) or weight <= 0:
            raise ValueError("weighted_laplacian requires finite positive weights")
        rows.extend((u, v))
        columns.extend((v, u))
        values.extend((-weight, -weight))
        diagonal[u] += weight
        diagonal[v] += weight
    matrix = sparse.coo_matrix((values, (rows, columns)), shape=(n, n)).tocsr()
    return matrix + sparse.diags(diagonal)


def _finite(value: object) -> float | None:
    if value is None:
        return None
    result = float(value)
    return result if math.isfinite(result) else None


def extract_injection_and_controls(network, graph: nx.Graph) -> dict:
    """Extract net active injection and the two operational control supports."""
    node_for_bus = {int(graph.nodes[node]["bus_id"]): node for node in graph.nodes()}
    n = graph.number_of_nodes()
    injection = np.zeros(n)
    positive_load_nodes: set[int] = set()
    for load in network.loads:
        if not load.get("in_service", True):
            continue
        node = node_for_bus.get(int(load["bus"]))
        demand = _finite(load.get("p"))
        if node is None or demand is None:
            continue
        injection[node] -= demand
        if demand > 0:
            positive_load_nodes.add(node)

    generation: dict[int, dict[str, float]] = {}
    for generator in network.generators:
        if not generator.get("in_service", True):
            continue
        node = node_for_bus.get(int(generator["bus"]))
        pg = _finite(generator.get("pg"))
        pmin = _finite(generator.get("pmin"))
        pmax = _finite(generator.get("pmax"))
        if node is None or pg is None:
            continue
        injection[node] += pg
        aggregate = generation.setdefault(
            node, {"pg": 0.0, "pmin": 0.0, "pmax": 0.0, "complete": 1.0}
        )
        aggregate["pg"] += pg
        if pmin is None or pmax is None:
            aggregate["complete"] = 0.0
        else:
            aggregate["pmin"] += pmin
            aggregate["pmax"] += pmax

    generator_controls = sorted(
        node
        for node, values in generation.items()
        if values["complete"]
        and values["pg"] > values["pmin"] + 1e-9
        and values["pg"] < values["pmax"] - 1e-9
    )
    flexible_controls = sorted(set(generator_controls) | positive_load_nodes)

    reference_bus_ids = sorted(
        int(bus["id"])
        for bus in network.buses
        if str(bus.get("kind", "")).upper() == "REF" and int(bus["id"]) in node_for_bus
    )
    if not reference_bus_ids:
        return {
            "status": "unavailable",
            "reason": "no recorded reference bus in retained component",
            "generator_controls": generator_controls,
            "flexible_controls": flexible_controls,
        }
    reference_bus_id = reference_bus_ids[0]
    residual = float(np.sum(injection))
    injection[node_for_bus[reference_bus_id]] -= residual
    return {
        "status": "computed",
        "injection": injection,
        "reference_bus_id": reference_bus_id,
        "reference_bus_ids": reference_bus_ids,
        "reference_nodes": [node_for_bus[bus_id] for bus_id in reference_bus_ids],
        "pre_balance_residual": residual,
        "post_balance_residual": float(np.sum(injection)),
        "generator_controls": generator_controls,
        "flexible_controls": flexible_controls,
    }


def _phase_invariant_distance(first: np.ndarray, second: np.ndarray) -> float:
    first_norm = float(np.linalg.norm(first))
    second_norm = float(np.linalg.norm(second))
    if first_norm == 0 or second_norm == 0:
        raise ValueError("state distance is undefined for a zero vector")
    overlap = abs(float(np.dot(first, second) / (first_norm * second_norm)))
    return math.sqrt(max(0.0, 2.0 - 2.0 * min(1.0, overlap)))


def _verdict(value: float, threshold: float = PRIMARY_RATIO) -> str:
    if value > threshold + NUMERICAL_MARGIN:
        return "pass"
    if value < threshold - NUMERICAL_MARGIN:
        return "fail"
    return "indeterminate"


@dataclass
class LaplacianAnalyzer:
    """Validated solves and spectral data for one fixed weighted topology."""

    laplacian: sparse.csr_matrix
    graph: nx.Graph
    dense_limit: int = 1500
    grounded_n_limit: int = 2500
    restricted_n_limit: int = 10_000
    restricted_control_limit: int = 750

    def __post_init__(self) -> None:
        self.n = self.laplacian.shape[0]
        if self.n < 2:
            raise ValueError("conditioning requires at least two retained buses")
        self._dense_vectors: np.ndarray | None = None
        self._positive_eigenvalues: np.ndarray | None = None
        self._low_vectors: np.ndarray | None = None
        self._low_values: np.ndarray | None = None
        self._factor = None
        self._restricted_cache: dict[tuple[int, ...], dict] = {}
        self._compute_spectrum()

    def _compute_spectrum(self) -> None:
        if self.n <= self.dense_limit:
            values, vectors = np.linalg.eigh(self.laplacian.toarray())
            scale = max(1.0, abs(float(values[-1])))
            if abs(float(values[0])) > 1e-8 * scale or float(values[1]) <= 1e-10 * scale:
                raise ValueError("dense eigendecomposition did not find one zero mode")
            self.lambda_two = float(values[1])
            self.lambda_maximum = float(values[-1])
            self._positive_eigenvalues = values[1:]
            self._dense_vectors = vectors[:, 1:]
            self._low_values = values[1:]
            self._low_vectors = vectors[:, 1:]
            self.spectral_method = "dense-eigh"
        else:
            generator = np.random.default_rng(42)
            start = generator.standard_normal(self.n)
            largest_values, largest_vectors = sparse_linalg.eigsh(
                self.laplacian,
                k=1,
                which="LA",
                v0=start,
                tol=1e-10,
                maxiter=max(10_000, 20 * self.n),
            )
            self.lambda_maximum = float(largest_values[0])
            shift = 2 * max(1.0, self.lambda_maximum)
            ones = np.ones(self.n)
            operator = sparse_linalg.LinearOperator(
                (self.n, self.n),
                matvec=lambda vector: self.laplacian @ vector
                + shift * float(np.mean(vector)) * ones,
                dtype=np.float64,
            )
            low_start = generator.standard_normal(self.n)
            low_start -= np.mean(low_start)
            count = min(32, self.n - 1)
            low_values, low_vectors = sparse_linalg.eigsh(
                operator,
                k=count,
                which="SA",
                v0=low_start,
                tol=1e-9,
                maxiter=max(10_000, 20 * self.n),
            )
            order = np.argsort(low_values)
            self._low_values = low_values[order]
            self._low_vectors = low_vectors[:, order]
            self.lambda_two = float(self._low_values[0])
            self.spectral_method = "eigsh-nullspace-shifted"
            self._largest_vector = largest_vectors[:, 0]

        scale = max(1.0, self.lambda_maximum)
        vector_two = self._low_vectors[:, 0]
        vector_maximum = (
            self._dense_vectors[:, -1]
            if self._dense_vectors is not None
            else self._largest_vector
        )
        self.residual_two = float(
            np.linalg.norm(self.laplacian @ vector_two - self.lambda_two * vector_two)
            / scale
        )
        self.residual_maximum = float(
            np.linalg.norm(
                self.laplacian @ vector_maximum - self.lambda_maximum * vector_maximum
            )
            / scale
        )
        self.orthogonality_residual = float(
            np.linalg.norm(
                self._low_vectors.T @ self._low_vectors
                - np.eye(self._low_vectors.shape[1])
            )
        )
        self.null_residual = float(
            np.linalg.norm(self.laplacian @ np.ones(self.n))
            / (scale * math.sqrt(self.n))
        )
        if max(self.residual_two, self.residual_maximum, self.null_residual) > 1e-7:
            raise ValueError("spectral residual exceeds 1e-7")

    @property
    def kappa(self) -> float:
        return self.lambda_maximum / self.lambda_two

    def _ensure_factor(self) -> None:
        if self._factor is not None:
            return
        reduced = self.laplacian[1:, 1:].tocsc()
        self._factor = sparse_linalg.splu(reduced)

    def solve(self, rhs: np.ndarray) -> tuple[np.ndarray, float]:
        rhs = np.asarray(rhs, dtype=float)
        if rhs.shape != (self.n,):
            raise ValueError("right hand side has the wrong shape")
        balanced = rhs - float(np.mean(rhs))
        self._ensure_factor()
        solution = np.zeros(self.n)
        solution[1:] = self._factor.solve(balanced[1:])
        solution -= float(np.mean(solution))
        denominator = max(float(np.linalg.norm(balanced)), 1.0)
        residual = float(np.linalg.norm(self.laplacian @ solution - balanced) / denominator)
        if residual > 1e-7:
            raise ValueError(f"linear solve residual {residual:.3e} exceeds tolerance")
        return solution, residual

    def _effective_metrics(self, solution: np.ndarray) -> dict:
        state = solution / np.linalg.norm(solution)
        coefficients = self._low_vectors.T @ state
        masses = coefficients**2
        threshold_mask = self._low_values <= 2 * self.lambda_two * (1 + 1e-8)
        low_mass = float(np.sum(masses[threshold_mask]))
        values: dict[str, dict] = {}
        if self._dense_vectors is not None:
            all_coefficients = self._dense_vectors.T @ state
            all_masses = all_coefficients**2
            reconstruction = float(
                np.linalg.norm(self._dense_vectors @ all_coefficients - state)
            )
            for epsilon in EFFECTIVE_EPSILONS:
                cumulative = np.cumsum(all_masses)
                index = int(np.searchsorted(cumulative, epsilon**2, side="right"))
                index = min(index, len(self._positive_eigenvalues) - 1)
                effective = self.lambda_maximum / float(self._positive_eigenvalues[index])
                ratio = effective / self.kappa
                values[str(epsilon)] = {
                    "status": "computed",
                    "kappa_effective": effective,
                    "ratio_to_kappa": ratio,
                    "condition": _verdict(ratio),
                }
            method = "full-spectrum"
        else:
            reconstruction = None
            captured_past_threshold = bool(
                self._low_values[-1] > 2 * self.lambda_two * (1 + 1e-6)
            )
            for epsilon in EFFECTIVE_EPSILONS:
                if not captured_past_threshold:
                    condition = "indeterminate"
                elif low_mass > epsilon**2 + NUMERICAL_MARGIN * epsilon**2:
                    condition = "pass"
                elif low_mass < epsilon**2 - NUMERICAL_MARGIN * epsilon**2:
                    condition = "fail"
                else:
                    condition = "indeterminate"
                values[str(epsilon)] = {
                    "status": "threshold-certified" if captured_past_threshold else "indeterminate",
                    "kappa_effective": None,
                    "ratio_to_kappa": None,
                    "condition": condition,
                }
            method = "low-spectrum-threshold"
        return {
            "method": method,
            "low_spectral_solution_mass": low_mass,
            "reconstruction_residual": reconstruction,
            "epsilon": values,
        }

    def analyze_rhs(self, injection: np.ndarray) -> dict:
        norm = float(np.linalg.norm(injection))
        if norm <= 1e-14:
            return {"status": "unavailable", "reason": "balanced injection is zero"}
        try:
            solution, residual = self.solve(injection)
            second_solution, second_residual = self.solve(solution)
        except (RuntimeError, ValueError) as error:
            return {"status": "indeterminate", "reason": str(error)}
        solution_norm = float(np.linalg.norm(solution))
        if solution_norm <= 1e-14:
            return {"status": "unavailable", "reason": "solution is zero"}
        effective = self._effective_metrics(solution)
        return {
            "status": "computed",
            "kappa": self.kappa,
            "rhs_solution_state_distance": _phase_invariant_distance(injection, solution),
            "filtering_factor": self.lambda_two
            * float(np.linalg.norm(second_solution))
            / solution_norm,
            "low_spectral_solution_mass": effective["low_spectral_solution_mass"],
            "effective_conditioning": effective,
            "primary_condition": effective["epsilon"]["0.01"]["condition"],
            "solver_residual": residual,
            "second_solver_residual": second_residual,
            "spectral_residual_lambda_two": self.residual_two,
            "spectral_residual_lambda_maximum": self.residual_maximum,
            "spectral_orthogonality_residual": self.orthogonality_residual,
            "null_residual": self.null_residual,
        }

    def analyze_grounded_slacks(self, slack_nodes: list[int]) -> dict:
        """Report grounded condition numbers separately from the balanced analysis."""
        if self.n > self.grounded_n_limit:
            return {
                "status": "indeterminate",
                "reason": "grounded sensitivity size limit",
                "maximum_n": self.grounded_n_limit,
            }
        results = []
        for slack in slack_nodes:
            retained = np.arange(self.n) != slack
            grounded = self.laplacian[retained][:, retained].tocsr()
            if grounded.shape[0] <= self.dense_limit:
                values = np.linalg.eigvalsh(grounded.toarray())
                minimum = float(values[0])
                maximum = float(values[-1])
                method = "dense-eigvalsh"
                residual_minimum = residual_maximum = 0.0
            else:
                start = np.random.default_rng(42).standard_normal(grounded.shape[0])
                minimum_values, minimum_vectors = sparse_linalg.eigsh(
                    grounded,
                    k=1,
                    which="SA",
                    v0=start,
                    tol=1e-9,
                    maxiter=max(10_000, 20 * grounded.shape[0]),
                )
                maximum_values, maximum_vectors = sparse_linalg.eigsh(
                    grounded,
                    k=1,
                    which="LA",
                    v0=start,
                    tol=1e-9,
                    maxiter=max(10_000, 20 * grounded.shape[0]),
                )
                minimum = float(minimum_values[0])
                maximum = float(maximum_values[0])
                scale = max(1.0, maximum)
                residual_minimum = float(
                    np.linalg.norm(
                        grounded @ minimum_vectors[:, 0]
                        - minimum * minimum_vectors[:, 0]
                    )
                    / scale
                )
                residual_maximum = float(
                    np.linalg.norm(
                        grounded @ maximum_vectors[:, 0]
                        - maximum * maximum_vectors[:, 0]
                    )
                    / scale
                )
                method = "eigsh"
            if minimum <= 0 or max(residual_minimum, residual_maximum) > 1e-7:
                return {
                    "status": "indeterminate",
                    "reason": "invalid grounded spectrum",
                    "slack_node": slack,
                }
            results.append(
                {
                    "slack_node": slack,
                    "slack_bus_id": str(self.graph.nodes[slack]["bus_id"]),
                    "method": method,
                    "lambda_minimum": minimum,
                    "lambda_maximum": maximum,
                    "condition_number": maximum / minimum,
                    "ratio_to_balanced_kappa": (maximum / minimum) / self.kappa,
                    "residual_minimum": residual_minimum,
                    "residual_maximum": residual_maximum,
                }
            )
        return {"status": "computed", "slacks": results}

    def analyze_subspace(self, controls: list[int]) -> dict:
        key = tuple(sorted(set(controls)))
        if key in self._restricted_cache:
            return self._restricted_cache[key]
        if len(key) < 2:
            result = {
                "status": "unavailable",
                "reason": "fewer than two admissible control buses",
                "control_buses": len(key),
            }
            self._restricted_cache[key] = result
            return result
        if self.n > self.restricted_n_limit or len(key) > self.restricted_control_limit:
            result = {
                "status": "indeterminate",
                "reason": "restricted SVD size limit",
                "control_buses": len(key),
                "n_limit": self.restricted_n_limit,
                "control_limit": self.restricted_control_limit,
            }
            self._restricted_cache[key] = result
            return result

        basis_on_support = linalg.helmert(len(key), full=False).T
        basis = np.zeros((self.n, len(key) - 1))
        basis[np.asarray(key), :] = basis_on_support
        self._ensure_factor()
        solutions = np.zeros_like(basis)
        solutions[1:, :] = self._factor.solve(basis[1:, :])
        solutions -= np.mean(solutions, axis=0, keepdims=True)
        reconstruction = self.laplacian @ solutions - basis
        residual = float(np.linalg.norm(reconstruction) / max(np.linalg.norm(basis), 1.0))
        if residual > 1e-7:
            result = {
                "status": "indeterminate",
                "reason": f"restricted solve residual {residual:.3e}",
                "control_buses": len(key),
            }
            self._restricted_cache[key] = result
            return result
        left, singular, right_transpose = np.linalg.svd(solutions, full_matrices=False)
        sigma_max = float(singular[0])
        sigma_min = float(singular[-1])
        if sigma_min <= 0:
            result = {
                "status": "indeterminate",
                "reason": "nonpositive restricted minimum singular value",
                "control_buses": len(key),
            }
            self._restricted_cache[key] = result
            return result
        kappa_s = sigma_max / sigma_min
        ratio = kappa_s / self.kappa
        if len(singular) < 2:
            result = {
                "status": "computed",
                "control_buses": len(key),
                "kappa_restricted": kappa_s,
                "ratio_to_kappa": ratio,
                "condition": _verdict(ratio),
                "sigma_max_inverse": sigma_max,
                "sigma_min_inverse": sigma_min,
                "restricted_solve_residual": residual,
                "singular_value_residual_max": float(
                    np.linalg.norm(
                        solutions @ right_transpose[0] - sigma_max * left[:, 0]
                    )
                ),
                "singular_value_residual_min": 0.0,
                "hard_pair_subspace_residual": 0.0,
                "hard_pair": {
                    "status": "unavailable",
                    "reason": "admissible balanced subspace has dimension one",
                },
                "observable": {
                    "status": "unavailable",
                    "reason": "two orthogonal extreme modes do not exist",
                },
            }
            self._restricted_cache[key] = result
            return result
        mode_max = left[:, 0]
        mode_min = left[:, -1]
        bus_gaps = 2 * np.abs(mode_min * mode_max)
        best_bus = int(np.argmax(bus_gaps))
        branch_records = [
            (
                2
                * abs((mode_min[u] - mode_min[v]) * (mode_max[u] - mode_max[v])),
                u,
                v,
            )
            for u, v in self.graph.edges()
        ]
        best_branch_gap, branch_u, branch_v = max(branch_records, default=(0.0, -1, -1))
        normalized_branch_gap = best_branch_gap / 2
        best_normalized_gap = max(float(bus_gaps[best_bus]), normalized_branch_gap)
        local_status = "pass" if best_normalized_gap > 1e-10 else "indeterminate"
        hard_plus = basis @ right_transpose[-1] + (basis @ right_transpose[0]) / kappa_s
        hard_minus = basis @ right_transpose[-1] - (basis @ right_transpose[0]) / kappa_s
        hard_solution_plus = solutions @ right_transpose[-1] + (
            solutions @ right_transpose[0]
        ) / kappa_s
        hard_solution_minus = solutions @ right_transpose[-1] - (
            solutions @ right_transpose[0]
        ) / kappa_s
        subspace_residual = max(
            abs(float(np.sum(hard_plus))),
            abs(float(np.sum(hard_minus))),
            float(np.linalg.norm(hard_plus[np.setdiff1d(np.arange(self.n), key)])),
            float(np.linalg.norm(hard_minus[np.setdiff1d(np.arange(self.n), key)])),
        )
        result = {
            "status": "computed",
            "control_buses": len(key),
            "kappa_restricted": kappa_s,
            "ratio_to_kappa": ratio,
            "condition": _verdict(ratio),
            "sigma_max_inverse": sigma_max,
            "sigma_min_inverse": sigma_min,
            "restricted_solve_residual": residual,
            "singular_value_residual_max": float(
                np.linalg.norm(solutions @ right_transpose[0] - sigma_max * mode_max)
            ),
            "singular_value_residual_min": float(
                np.linalg.norm(solutions @ right_transpose[-1] - sigma_min * mode_min)
            ),
            "hard_pair_subspace_residual": subspace_residual,
            "hard_pair_input_state_distance": _phase_invariant_distance(
                hard_plus, hard_minus
            ),
            "hard_pair_expected_input_state_distance": math.sqrt(
                4 / (kappa_s**2 + 1)
            ),
            "hard_pair_solution_state_distance": _phase_invariant_distance(
                hard_solution_plus, hard_solution_minus
            ),
            "hard_pair_expected_solution_state_distance": math.sqrt(2.0),
            "hard_pair": {"status": "computed"},
            "observable": {
                "status": local_status,
                "best_normalized_gap": best_normalized_gap,
                "bus": {
                    "node": best_bus,
                    "bus_id": str(self.graph.nodes[best_bus]["bus_id"]),
                    "gap": float(bus_gaps[best_bus]),
                    "normalized_gap": float(bus_gaps[best_bus]),
                },
                "branch": {
                    "nodes": [branch_u, branch_v],
                    "bus_ids": (
                        [
                            str(self.graph.nodes[branch_u]["bus_id"]),
                            str(self.graph.nodes[branch_v]["bus_id"]),
                        ]
                        if branch_u >= 0
                        else None
                    ),
                    "gap": best_branch_gap,
                    "normalized_gap": normalized_branch_gap,
                },
            },
        }
        self._restricted_cache[key] = result
        return result


def analyze_operating_point(network, graph: nx.Graph, analyzer: LaplacianAnalyzer) -> dict:
    """Run base right hand side and both admissible subspace checks."""
    extracted = extract_injection_and_controls(network, graph)
    metadata = {key: value for key, value in extracted.items() if key != "injection"}
    if extracted["status"] != "computed":
        return {"status": "unavailable", "extraction": metadata}
    return {
        "status": "computed",
        "extraction": metadata,
        "base_rhs": analyzer.analyze_rhs(extracted["injection"]),
        "grounded_slack_sensitivity": analyzer.analyze_grounded_slacks(
            extracted["reference_nodes"]
        ),
        "generator_redispatch": analyzer.analyze_subspace(
            extracted["generator_controls"]
        ),
        "generator_load_redispatch": analyzer.analyze_subspace(
            extracted["flexible_controls"]
        ),
    }


def controlled_corridor(length: int, rhs_kind: str) -> dict:
    """Analyze a unit weight path with a selected right hand side family."""
    if length < 3:
        raise ValueError("corridor length must be at least three")
    graph = nx.path_graph(length)
    nx.set_node_attributes(graph, {node: str(node) for node in graph}, "bus_id")
    weights = {tuple(edge): 1.0 for edge in graph.edges()}
    analyzer = LaplacianAnalyzer(weighted_laplacian(length, weights), graph)
    if rhs_kind == "easy-eigenvector":
        rhs = analyzer._dense_vectors[:, -1]
    elif rhs_kind == "sparse-endpoints":
        rhs = np.zeros(length)
        rhs[0], rhs[-1] = 1.0, -1.0
    elif rhs_kind == "hard-pair-plus":
        rhs = analyzer._dense_vectors[:, -1] + analyzer._dense_vectors[:, 0] / analyzer.kappa
    else:
        raise ValueError(f"unknown corridor right hand side: {rhs_kind}")
    return {
        "length": length,
        "rhs_kind": rhs_kind,
        "base_rhs": analyzer.analyze_rhs(rhs),
    }
