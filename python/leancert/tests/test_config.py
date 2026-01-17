# LeanCert v2 SDK - Configuration Tests
# Copyright (c) 2025 LeanCert Contributors. All rights reserved.

"""
Tests for the configuration module including Backend selection,
DyadicConfig, AffineConfig, and Config factory methods.
"""

import pytest
from fractions import Fraction

from leancert.config import Backend, Config, DyadicConfig, AffineConfig


class TestBackendEnum:
    """Tests for the Backend enum."""

    def test_backend_values(self):
        """Test that backend enum has expected values."""
        assert Backend.RATIONAL.value == "rational"
        assert Backend.DYADIC.value == "dyadic"
        assert Backend.AFFINE.value == "affine"

    def test_backend_from_string(self):
        """Test creating backend from string value."""
        assert Backend("rational") == Backend.RATIONAL
        assert Backend("dyadic") == Backend.DYADIC
        assert Backend("affine") == Backend.AFFINE

    def test_backend_invalid_value(self):
        """Test that invalid backend value raises error."""
        with pytest.raises(ValueError):
            Backend("invalid")


class TestDyadicConfig:
    """Tests for DyadicConfig."""

    def test_default_values(self):
        """Test default configuration values."""
        cfg = DyadicConfig()
        assert cfg.precision == -53
        assert cfg.round_after_ops == 0

    def test_custom_precision(self):
        """Test custom precision setting."""
        cfg = DyadicConfig(precision=-100)
        assert cfg.precision == -100

    def test_ieee_double_preset(self):
        """Test IEEE double preset."""
        cfg = DyadicConfig.ieee_double()
        assert cfg.precision == -53

    def test_high_precision_preset(self):
        """Test high precision preset."""
        cfg = DyadicConfig.high_precision()
        assert cfg.precision == -100

    def test_fast_preset(self):
        """Test fast preset."""
        cfg = DyadicConfig.fast()
        assert cfg.precision == -30


class TestAffineConfig:
    """Tests for AffineConfig."""

    def test_default_values(self):
        """Test default configuration values."""
        cfg = AffineConfig()
        assert cfg.max_noise_symbols == 0

    def test_custom_max_symbols(self):
        """Test custom max noise symbols."""
        cfg = AffineConfig(max_noise_symbols=50)
        assert cfg.max_noise_symbols == 50

    def test_default_preset(self):
        """Test default preset."""
        cfg = AffineConfig.default()
        assert cfg.max_noise_symbols == 0

    def test_compact_preset(self):
        """Test compact preset."""
        cfg = AffineConfig.compact()
        assert cfg.max_noise_symbols == 100


class TestConfig:
    """Tests for the main Config class."""

    def test_default_values(self):
        """Test default configuration values."""
        cfg = Config()
        assert cfg.taylor_depth == 10
        assert cfg.max_iters == 1000
        assert cfg.tolerance == Fraction(1, 1000)
        assert cfg.use_monotonicity is True
        assert cfg.timeout_sec == 60.0
        assert cfg.backend == Backend.RATIONAL
        assert cfg.dyadic_config is None
        assert cfg.affine_config is None

    def test_custom_values(self):
        """Test custom configuration values."""
        cfg = Config(
            taylor_depth=15,
            max_iters=2000,
            tolerance=Fraction(1, 10000),
            use_monotonicity=False,
            timeout_sec=120.0,
        )
        assert cfg.taylor_depth == 15
        assert cfg.max_iters == 2000
        assert cfg.tolerance == Fraction(1, 10000)
        assert cfg.use_monotonicity is False
        assert cfg.timeout_sec == 120.0

    def test_tolerance_float_conversion(self):
        """Test that float tolerance is converted to Fraction."""
        cfg = Config(tolerance=0.001)
        assert isinstance(cfg.tolerance, Fraction)
        # Should be close to 1/1000
        assert abs(float(cfg.tolerance) - 0.001) < 1e-10

    def test_dyadic_backend_auto_config(self):
        """Test that dyadic backend auto-creates DyadicConfig."""
        cfg = Config(backend=Backend.DYADIC)
        assert cfg.backend == Backend.DYADIC
        assert cfg.dyadic_config is not None
        assert isinstance(cfg.dyadic_config, DyadicConfig)

    def test_affine_backend_auto_config(self):
        """Test that affine backend auto-creates AffineConfig."""
        cfg = Config(backend=Backend.AFFINE)
        assert cfg.backend == Backend.AFFINE
        assert cfg.affine_config is not None
        assert isinstance(cfg.affine_config, AffineConfig)

    def test_explicit_dyadic_config(self):
        """Test explicit DyadicConfig is preserved."""
        dyadic_cfg = DyadicConfig(precision=-80)
        cfg = Config(backend=Backend.DYADIC, dyadic_config=dyadic_cfg)
        assert cfg.dyadic_config.precision == -80

    def test_explicit_affine_config(self):
        """Test explicit AffineConfig is preserved."""
        affine_cfg = AffineConfig(max_noise_symbols=50)
        cfg = Config(backend=Backend.AFFINE, affine_config=affine_cfg)
        assert cfg.affine_config.max_noise_symbols == 50


class TestConfigPresets:
    """Tests for Config factory methods / presets."""

    def test_low_precision(self):
        """Test low precision preset."""
        cfg = Config.low_precision()
        assert cfg.taylor_depth == 5
        assert cfg.max_iters == 100
        assert cfg.tolerance == Fraction(1, 100)

    def test_medium_precision(self):
        """Test medium precision preset (default)."""
        cfg = Config.medium_precision()
        assert cfg.taylor_depth == 10
        assert cfg.max_iters == 1000

    def test_high_precision(self):
        """Test high precision preset."""
        cfg = Config.high_precision()
        assert cfg.taylor_depth == 20
        assert cfg.max_iters == 5000
        assert cfg.tolerance == Fraction(1, 100000)

    def test_dyadic_preset(self):
        """Test dyadic preset."""
        cfg = Config.dyadic()
        assert cfg.backend == Backend.DYADIC
        assert cfg.dyadic_config is not None
        assert cfg.dyadic_config.precision == -53

    def test_dyadic_custom_precision(self):
        """Test dyadic preset with custom precision."""
        cfg = Config.dyadic(precision=-80)
        assert cfg.backend == Backend.DYADIC
        assert cfg.dyadic_config.precision == -80

    def test_dyadic_fast_preset(self):
        """Test dyadic fast preset."""
        cfg = Config.dyadic_fast()
        assert cfg.backend == Backend.DYADIC
        assert cfg.dyadic_config.precision == -30
        assert cfg.taylor_depth == 8

    def test_dyadic_high_precision_preset(self):
        """Test dyadic high precision preset."""
        cfg = Config.dyadic_high_precision()
        assert cfg.backend == Backend.DYADIC
        assert cfg.dyadic_config.precision == -100
        assert cfg.taylor_depth == 20

    def test_affine_preset(self):
        """Test affine preset."""
        cfg = Config.affine()
        assert cfg.backend == Backend.AFFINE
        assert cfg.affine_config is not None
        assert cfg.affine_config.max_noise_symbols == 0

    def test_affine_compact_preset(self):
        """Test affine compact preset."""
        cfg = Config.affine_compact()
        assert cfg.backend == Backend.AFFINE
        assert cfg.affine_config.max_noise_symbols == 100


class TestConfigKernelConversion:
    """Tests for Config conversion to kernel format."""

    def test_to_kernel(self):
        """Test conversion to kernel-compatible format."""
        cfg = Config(
            taylor_depth=15,
            max_iters=500,
            tolerance=Fraction(1, 1000),
            use_monotonicity=True,
        )
        kernel = cfg.to_kernel()
        assert kernel['taylorDepth'] == 15
        assert kernel['maxIters'] == 500
        assert kernel['tolerance'] == {'n': 1, 'd': 1000}
        assert kernel['useMonotonicity'] is True

    def test_to_dyadic_kernel(self):
        """Test conversion to dyadic kernel format."""
        cfg = Config.dyadic(precision=-80)
        cfg.taylor_depth = 12
        kernel = cfg.to_dyadic_kernel()
        assert kernel['precision'] == -80
        assert kernel['taylorDepth'] == 12
        assert kernel['roundAfterOps'] == 0

    def test_to_affine_kernel(self):
        """Test conversion to affine kernel format."""
        cfg = Config.affine_compact()
        cfg.taylor_depth = 8
        kernel = cfg.to_affine_kernel()
        assert kernel['taylorDepth'] == 8
        assert kernel['maxNoiseSymbols'] == 100


class TestConfigRepr:
    """Tests for Config string representation."""

    def test_repr_rational(self):
        """Test repr for rational backend."""
        cfg = Config()
        repr_str = repr(cfg)
        assert "taylor_depth=10" in repr_str
        assert "backend" not in repr_str  # Not shown for default

    def test_repr_dyadic(self):
        """Test repr for dyadic backend."""
        cfg = Config.dyadic()
        repr_str = repr(cfg)
        assert "backend=dyadic" in repr_str

    def test_repr_affine(self):
        """Test repr for affine backend."""
        cfg = Config.affine()
        repr_str = repr(cfg)
        assert "backend=affine" in repr_str
