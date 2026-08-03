# Installation and Compatibility

## Install

```bash
python -m pip install leancert
```

LeanCert Python 1.0 requires Python 3.10 or newer and depends on NumPy. PyTorch
support is optional:

```bash
python -m pip install 'leancert[pytorch]'
```

## Bundled Bridge platforms

The 1.0 release publishes wheels for:

- Linux x86-64;
- macOS arm64;
- macOS x86-64; and
- Windows x86-64.

Supported wheels include a version-pinned `lean_bridge` binary. Installing from
an sdist or running on an unsupported platform may require an explicitly built
Bridge:

```bash
export LEANCERT_BRIDGE_PATH=/absolute/path/to/lean_bridge
leancert doctor
```

## Contract negotiation

The SDK checks the Bridge API major version, operation schemas, advertised
capabilities, certificate families, backends, and verification routes before
sending checked work. Unknown major versions and contradictory responses are
rejected rather than guessed compatible.

## Core, Bridge, and SDK versions

The Python package, Bridge, and LeanCert Core have separate release numbers.
Use `leancert doctor --json` or a result's `provenance` instead of inferring one
component's version from another.

## Legacy API migration

The pre-1.0 API remains available:

```python
x = lc.var("x")
with lc.Solver() as solver:
    result = solver.find_bounds(x**2, {"x": (-1, 1)})
```

New proof-oriented code should use:

```python
x = ast.var("x")
result = lc.prove(x**2 <= 1, where={x: (-1, 1)})
```

The semantic API adds exact input enforcement, claim normalization, stable
identity, typed non-success, and replay export. Use explicit `ast.legacy_*`
adapters when crossing the boundary.
