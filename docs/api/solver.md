# Solver API

The `Solver` class is the main entry point for the Python SDK. It manages communication with the Lean kernel and handles the verification lifecycle.

## Solver Class

::: leanbound.solver.Solver
    options:
      members:
        - __init__
        - find_bounds
        - find_roots
        - find_unique_root
        - verify_bound
        - integrate
      show_root_heading: true
      show_source: false

## Convenience Functions

These standalone functions use a default solver instance for quick scripting.

::: leanbound.solver.find_bounds

::: leanbound.solver.find_roots

::: leanbound.solver.find_unique_root

::: leanbound.solver.verify_bound

::: leanbound.solver.integrate
