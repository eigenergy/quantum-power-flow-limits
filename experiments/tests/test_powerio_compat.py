"""Pin the PowerIO surface the structural pipeline reads.

The structural scripts touch a small PowerIO surface: ``parse_file``,
``__version__``, ``len(network.buses)``, branch rows through the
``in_service``, ``from_id``, ``to_id``, and ``x`` fields, and
``to_networkx``. These tests state that surface against an installed
PowerIO wheel, so an upstream change surfaces here before it reaches a
survey run. The locked experiment environment does not carry PowerIO;
the tests skip there and run in the dedicated compatibility CI job.
``scripts/qpf_model.py`` consumes exactly this surface, so its export
tests live here and run against the same installed wheel.
"""

import math
import re
import sys
from fractions import Fraction
from pathlib import Path

import pytest

powerio = pytest.importorskip("powerio")

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))

import qpf_cert
import qpf_model

CASE3 = """function mpc = case3
mpc.version = '2';
mpc.baseMVA = 100;
mpc.bus = [
\t1\t3\t0\t0\t0\t0\t1\t1\t0\t345\t1\t1.1\t0.9;
\t2\t1\t50\t10\t0\t0\t1\t1\t0\t345\t1\t1.1\t0.9;
\t3\t1\t60\t15\t0\t0\t1\t1\t0\t345\t1\t1.1\t0.9;
];
mpc.gen = [
\t1\t100\t0\t300\t-300\t1\t100\t1\t250\t10\t0\t0\t0\t0\t0\t0\t0\t0\t0\t0\t0;
];
mpc.gencost = [
\t2\t0\t0\t3\t0.01\t40\t0;
];
mpc.branch = [
\t1\t2\t0.01\t0.06\t0\t250\t250\t250\t0\t0\t1\t-360\t360;
\t1\t3\t0.02\t0.09\t0\t250\t250\t250\t0\t0\t1\t-360\t360;
\t2\t3\t0.03\t0.08\t0\t250\t250\t250\t0\t0\t1\t-360\t360;
];
"""


@pytest.fixture()
def network(tmp_path):
    path = tmp_path / "case3.m"
    path.write_text(CASE3, encoding="ascii")
    return powerio.parse_file(path)


def test_version_states_a_release():
    assert isinstance(powerio.__version__, str)
    assert re.fullmatch(r"\d+\.\d+\.\d+", powerio.__version__)


def test_parse_file_returns_the_expected_tables(network):
    assert len(network.buses) == 3
    assert len(network.branches) == 3


def test_branch_rows_carry_the_structural_fields(network):
    reactances = []
    for branch in network.branches:
        assert bool(branch["in_service"]) is True
        assert int(branch["from_id"]) != int(branch["to_id"])
        reactance = float(branch["x"])
        assert math.isfinite(reactance)
        reactances.append(reactance)
    assert sorted(reactances) == pytest.approx([0.06, 0.08, 0.09])


def test_to_networkx_matches_the_branch_rows(network):
    graph = network.to_networkx()
    assert not graph.is_directed()
    assert graph.number_of_nodes() == 3
    assert graph.number_of_edges() == 3
    nodes = set(graph.nodes())
    for branch in network.branches:
        assert int(branch["from_id"]) in nodes
        assert int(branch["to_id"]) in nodes


def test_qpf_model_dyadic_is_exact_and_odd():
    assert qpf_model.dyadic(0.5) == (1, -1)
    assert qpf_model.dyadic(3.0) == (3, 0)
    weight = 1 / 0.06
    significand, exponent = qpf_model.dyadic(weight)
    assert significand % 2 == 1
    assert Fraction(significand) * Fraction(2) ** exponent == Fraction(
        *weight.as_integer_ratio()
    )


def test_qpf_model_exports_exact_dyadic_weights(tmp_path):
    path = tmp_path / "case3.m"
    path.write_text(CASE3, encoding="ascii")
    document = qpf_model.export_model(path)
    tokens = document.split()
    assert tokens[:7] == ["QPFMODEL", "1", "N", "3", "M", "3", "BRANCHES"]
    assert tokens[-1] == "END"
    model_path = tmp_path / "case3.model.qpf"
    model_path.write_text(document, encoding="ascii")
    bus_count, branches = qpf_cert.parse_model(model_path)
    assert bus_count == 3
    weights = {(source, target): weight for source, target, weight in branches}
    assert weights == {
        (0, 1): Fraction(*(1 / 0.06).as_integer_ratio()),
        (0, 2): Fraction(*(1 / 0.09).as_integer_ratio()),
        (1, 2): Fraction(*(1 / 0.08).as_integer_ratio()),
    }


def test_qpf_model_refuses_nonpositive_reactance(tmp_path):
    path = tmp_path / "case3-zero-x.m"
    path.write_text(CASE3.replace("0.06", "0.00", 1), encoding="ascii")
    with pytest.raises(qpf_model.ExportError):
        qpf_model.export_model(path)
