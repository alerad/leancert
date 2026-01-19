# Expressions and Domains

## Building Expressions

LeanCert uses symbolic expressions that are reified to the Lean AST.

### Variables

```python
import leancert as lc

x = lc.var('x')
y = lc.var('y')
```

### Constants

```python
c = lc.const(3.14159)
half = lc.const(1, 2)  # Fraction 1/2
```

### Arithmetic

```python
expr = x**2 + 2*x + 1
expr = (x + y) / (x - y)
```

### Transcendental Functions

```python
lc.sin(x)
lc.cos(x)
lc.exp(x)
lc.log(x)
lc.sqrt(x)
lc.tan(x)
lc.atan(x)
lc.sinh(x)
lc.cosh(x)
lc.tanh(x)
lc.arsinh(x)
lc.atanh(x)
lc.abs(x)
```

### Special Functions

```python
lc.sinc(x)  # sin(x)/x with sinc(0) = 1
lc.erf(x)   # Error function
```

### Min/Max/Clamp

```python
lc.Min(x, y)
lc.Max(x, y)
lc.clamp(x, lo, hi)  # Equivalent to Min(Max(x, lo), hi)
```

## Domain Specification

### Intervals

```python
from leancert import Interval

I = Interval(0, 1)       # [0, 1]
I = Interval(-1, 1)      # [-1, 1]
I = Interval("1/3", 1)   # [1/3, 1] (exact rational)
```

### Boxes (Multi-dimensional)

```python
from leancert import Box

# Using a dictionary
box = Box({'x': (0, 1), 'y': (-1, 1)})

# Or pass directly to solver functions
result = lc.find_bounds(x + y, {'x': (0, 1), 'y': (0, 1)})
```

## Simplification

LeanCert includes symbolic simplification to mitigate the dependency problem in interval arithmetic.

::: leancert.simplify.simplify

::: leancert.simplify.expand

### Example

```python
x = lc.var('x')

# Without simplification, (x*100 + 5) - (x*100) on [0, 1e10]
# would give bounds like [-1e12, 1e12] due to dependency

# With simplification, it reduces to 5
expr = (x * 100 + 5) - (x * 100)
simplified = lc.simplify(expr)
# simplified is const(5)
```

## Expression Reference

::: leancert.expr.Expr
    options:
      show_root_heading: true
      members:
        - free_vars
        - substitute

::: leancert.expr.var

::: leancert.expr.const
