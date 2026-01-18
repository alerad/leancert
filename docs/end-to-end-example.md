# End-to-End Example: Python to Lean

This guide shows a complete workflow: explore in Python, generate a certificate, verify in Lean.

## The Problem

We want to prove that `x² + sin(x) ≤ 2` for all `x ∈ [0, 1]`.

## Step 1: Explore in Python

```python
import leancert as lc

# Define the expression
x = lc.var('x')
expr = x**2 + lc.sin(x)

# Find bounds on [0, 1]
result = lc.find_bounds(expr, {'x': (0, 1)})

print(f"Minimum: {result.min_bound}")  # ~0
print(f"Maximum: {result.max_bound}")  # ~1.84
```

Output:
```
Minimum: Interval(0, 0.001)
Maximum: Interval(1.83, 1.85)
```

The maximum is around 1.84, so `≤ 2` should be provable.

## Step 2: Verify the Bound

```python
# Verify our proposed bound
verified = lc.verify_bound(expr, {'x': (0, 1)}, upper=2)
print(f"Verified: {verified}")  # True
```

## Step 3: Generate Lean Code

```python
# Get the Lean tactic
print(result.certificate.to_lean_tactic())
```

Output:
```
certify_bound 10
```

## Step 4: Prove in Lean

Create a Lean file with the formal proof:

```lean
import LeanCert

-- The theorem we want to prove
theorem xsq_plus_sin_bounded :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x^2 + Real.sin x ≤ 2 := by
  certify_bound
```

That's it! The proof is now formally verified by Lean's kernel.

## Complete Working Example

### Python Script (`explore.py`)

```python
#!/usr/bin/env python3
import leancert as lc

# 1. Define expression
x = lc.var('x')
expr = x**2 + lc.sin(x)
domain = {'x': (0, 1)}

# 2. Explore bounds
print("=== Exploring x² + sin(x) on [0, 1] ===")
result = lc.find_bounds(expr, domain)
print(f"Range: [{result.min_bound.lo:.4f}, {result.max_bound.hi:.4f}]")

# 3. Verify specific bound
bound = 2
if lc.verify_bound(expr, domain, upper=bound):
    print(f"\n✓ Verified: x² + sin(x) ≤ {bound} on [0, 1]")
    print(f"\nLean proof:")
    print(f"  theorem my_bound : ∀ x ∈ Set.Icc (0:ℝ) 1, x^2 + Real.sin x ≤ {bound} := by")
    print(f"    certify_bound")
else:
    print(f"\n✗ Could not verify bound {bound}")

# 4. Find roots (bonus)
print("\n=== Finding roots of x² - 2 on [1, 2] ===")
roots = lc.find_roots(x**2 - 2, {'x': (1, 2)})
for r in roots.intervals:
    print(f"Root in [{r.lo:.6f}, {r.hi:.6f}]")
```

### Lean File (`Verified.lean`)

```lean
import LeanCert

/-!
# Verified Bounds

These theorems were discovered using the Python SDK and
formally verified by LeanCert.
-/

/-- x² + sin(x) ≤ 2 on [0, 1] -/
theorem xsq_plus_sin_le_2 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x^2 + Real.sin x ≤ 2 := by
  certify_bound

/-- √2 exists in [1, 2] -/
theorem sqrt2_exists :
    ∃ x ∈ Set.Icc (1 : ℝ) 2, x^2 = 2 := by
  interval_roots

/-- √2 is unique in [1, 2] -/
theorem sqrt2_unique :
    ∃! x ∈ Set.Icc (1 : ℝ) 2, x * x - 2 = 0 := by
  interval_unique_root
```

## Workflow Summary

```
┌─────────────────────────────────────────────────────────┐
│                      Python SDK                         │
│  • Symbolic expression building                         │
│  • Fast numerical exploration                           │
│  • Bound verification with false-positive filtering     │
│  • Certificate generation                               │
└─────────────────────────────────────────────────────────┘
                           │
                           ▼
                    ┌─────────────┐
                    │ Certificate │
                    │  (tactic +  │
                    │   params)   │
                    └─────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────┐
│                        Lean                             │
│  • Formal proof term generation                         │
│  • Kernel verification (no trust in Python)            │
│  • Auditable, reproducible guarantee                    │
└─────────────────────────────────────────────────────────┘
```

**Key insight**: Python is an untrusted oracle. It finds candidates quickly, but Lean independently verifies everything. A bug in Python cannot produce a false theorem—Lean's kernel is the final arbiter.
