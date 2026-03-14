# Security Policy

## Supported Versions

The following versions of OTLP Rust are currently supported with security updates:

| Version | Supported          | Rust Version |
| ------- | ------------------ | ------------ |
| 0.1.x   | :white_check_mark: | >= 1.94.0    |

## Reporting a Vulnerability

If you discover a security vulnerability in OTLP Rust, please report it responsibly.

### Reporting Process

1. **Do NOT** create a public GitHub issue for security vulnerabilities
2. Email security concerns to: [SECURITY CONTACT EMAIL]
3. Include the following information:
   - Description of the vulnerability
   - Steps to reproduce (if applicable)
   - Potential impact assessment
   - Suggested fix (if any)

### Response Timeline

- **Acknowledgment**: Within 48 hours
- **Initial Assessment**: Within 5 business days
- **Fix Timeline**: Based on severity
  - Critical: 7 days
  - High: 14 days
  - Medium: 30 days
  - Low: 90 days

## Security Measures

### Code Security

- Static analysis with Clippy
- Dependency scanning with cargo-audit
- License compliance with cargo-deny
- Regular security audits via GitHub Actions

### Dependencies

All dependencies are:

- Scanned for known vulnerabilities (daily)
- Checked for license compliance
- Reviewed for maintenance status

### Unsafe Code

This project uses unsafe code in limited, well-documented areas:

- SIMD optimizations
- Zero-copy buffer operations
- Performance-critical paths

All unsafe code blocks include:

- `SAFETY` comments explaining invariants
- Justification for unsafe usage
- Corresponding safety tests

## Security-Related Configuration

### Recommended Cargo.toml settings

```toml
[profile.release]
opt-level = 3
lto = "fat"
strip = "symbols"  # Reduces binary size and removes debug symbols
```

### Environment Variables

Secure handling of sensitive data:

- `OTEL_API_KEY`: API key for authentication
- `OTEL_CONFIG_FILE`: Path to configuration file
- Use environment-specific configuration files

## Known Security Considerations

### Network Security

- Default endpoints use TLS when available
- Certificate validation enabled by default
- Configurable timeout settings

### Data Handling

- No sensitive data logging in production
- Configurable compression (may affect security/performance trade-off)
- Batch processing to minimize network exposure

## Security Updates

Security updates will be announced via:

1. GitHub Security Advisories
2. Release notes
3. CHANGELOG.md

## Acknowledgments

We thank the following security researchers who have responsibly disclosed vulnerabilities:

_(None yet - this section will be updated as appropriate)_

---

**Last Updated**: 2026-03-15

For questions about this security policy, please open a discussion (not an issue) on GitHub.
