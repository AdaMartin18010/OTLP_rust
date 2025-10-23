# 🤝 Contributing to OTLP Rust

Thank you for your interest in contributing to OTLP Rust! This document provides guidelines for contributing to the project.

---

## 📋 Table of Contents

- [🤝 Contributing to OTLP Rust](#-contributing-to-otlp-rust)
  - [📋 Table of Contents](#-table-of-contents)
  - [📜 Code of Conduct](#-code-of-conduct)
    - [Our Standards](#our-standards)
  - [🚀 Getting Started](#-getting-started)
    - [Prerequisites](#prerequisites)
    - [First Steps](#first-steps)
  - [💻 Development Setup](#-development-setup)
    - [Install Dependencies](#install-dependencies)
    - [Build the Project](#build-the-project)
  - [🎯 How to Contribute](#-how-to-contribute)
    - [Types of Contributions](#types-of-contributions)
      - [🐛 Bug Fixes](#-bug-fixes)
      - [✨ New Features](#-new-features)
      - [📚 Documentation](#-documentation)
      - [🧪 Tests](#-tests)
      - [🎨 Code Quality](#-code-quality)
  - [📏 Coding Guidelines](#-coding-guidelines)
    - [Rust Style](#rust-style)
    - [Code Organization](#code-organization)
    - [Error Handling](#error-handling)
    - [Async Code](#async-code)
  - [🧪 Testing Guidelines](#-testing-guidelines)
    - [Test Organization](#test-organization)
    - [Test Coverage](#test-coverage)
    - [Running Tests](#running-tests)
  - [📚 Documentation Guidelines](#-documentation-guidelines)
    - [Code Documentation](#code-documentation)
    - [Documentation Files](#documentation-files)
    - [Example Code](#example-code)
  - [🔄 Pull Request Process](#-pull-request-process)
    - [Before Submitting](#before-submitting)
    - [Submitting the PR](#submitting-the-pr)
    - [PR Review Process](#pr-review-process)
    - [After Merge](#after-merge)
  - [🎓 Development Tips](#-development-tips)
    - [Useful Commands](#useful-commands)
    - [IDE Setup](#ide-setup)
  - [🌐 Community](#-community)
    - [Communication Channels](#communication-channels)
    - [Getting Help](#getting-help)
    - [Recognition](#recognition)
  - [📝 Commit Message Guidelines](#-commit-message-guidelines)
    - [Format](#format)
    - [Types](#types)
    - [Examples](#examples)
  - [🏆 Recognition](#-recognition)
    - [Hall of Fame](#hall-of-fame)
    - [Rewards](#rewards)
  - [📋 Checklist for First-Time Contributors](#-checklist-for-first-time-contributors)
  - [🙏 Thank You](#-thank-you)

---

## 📜 Code of Conduct

This project adheres to a code of conduct that we expect all contributors to follow. Please be respectful and constructive in your interactions.

### Our Standards

- ✅ Be welcoming and inclusive
- ✅ Be respectful of differing viewpoints
- ✅ Accept constructive criticism gracefully
- ✅ Focus on what is best for the community
- ✅ Show empathy towards other community members

---

## 🚀 Getting Started

### Prerequisites

- Rust 1.90.0 or later
- Git
- A GitHub account

### First Steps

1. **Fork the repository** on GitHub
2. **Clone your fork** locally:

   ```bash
   git clone https://github.com/YOUR_USERNAME/OTLP_rust.git
   cd OTLP_rust
   ```

3. **Add upstream remote**:

   ```bash
   git remote add upstream https://github.com/ORIGINAL_OWNER/OTLP_rust.git
   ```

4. **Create a branch**:

   ```bash
   git checkout -b feature/your-feature-name
   ```

---

## 💻 Development Setup

### Install Dependencies

```bash
# Install Rust (if not already installed)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Update Rust to latest stable
rustup update stable

# Install development tools
rustup component add rustfmt clippy
```

### Build the Project

```bash
# Build all crates
cargo build --workspace

# Build with all features
cargo build --all-features

# Run tests
cargo test --workspace

# Check formatting
cargo fmt --all -- --check

# Run clippy
cargo clippy --all-targets --all-features -- -D warnings
```

---

## 🎯 How to Contribute

### Types of Contributions

We welcome various types of contributions:

#### 🐛 Bug Fixes

- Search existing issues first
- Create a new issue if needed
- Submit a PR with the fix

#### ✨ New Features

- Discuss in an issue first
- Wait for approval before starting
- Submit a PR when ready

#### 📚 Documentation

- Fix typos and unclear explanations
- Add examples
- Improve guides

#### 🧪 Tests

- Add missing test coverage
- Improve test quality
- Add benchmark tests

#### 🎨 Code Quality

- Refactor existing code
- Improve performance
- Reduce technical debt

---

## 📏 Coding Guidelines

### Rust Style

Follow the [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/):

```rust
// ✅ Good: Clear, idiomatic Rust
pub struct OtlpClient {
    endpoint: String,
    config: ClientConfig,
}

impl OtlpClient {
    /// Creates a new OTLP client.
    ///
    /// # Examples
    ///
    /// ```
    /// use otlp::OtlpClient;
    ///
    /// let client = OtlpClient::new("http://localhost:4317");
    /// ```
    pub fn new(endpoint: &str) -> Self {
        Self {
            endpoint: endpoint.to_string(),
            config: ClientConfig::default(),
        }
    }
}
```

### Code Organization

- Keep modules focused and cohesive
- Use meaningful names
- Avoid deep nesting (max 3-4 levels)
- Prefer composition over inheritance

### Error Handling

```rust
// ✅ Use custom error types
use thiserror::Error;

#[derive(Error, Debug)]
pub enum OtlpError {
    #[error("Connection failed: {0}")]
    ConnectionError(String),
    
    #[error("Invalid configuration: {0}")]
    ConfigError(String),
}

// ✅ Use Result for fallible operations
pub fn connect(&self) -> Result<Connection, OtlpError> {
    // Implementation
}
```

### Async Code

```rust
// ✅ Use async/await idiomatically
pub async fn send_data(&self, data: &[u8]) -> Result<(), OtlpError> {
    let response = self.client
        .post(&self.endpoint)
        .body(data)
        .send()
        .await?;
    
    Ok(())
}
```

---

## 🧪 Testing Guidelines

### Test Organization

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_client_creation() {
        let client = OtlpClient::new("http://localhost:4317");
        assert_eq!(client.endpoint, "http://localhost:4317");
    }

    #[tokio::test]
    async fn test_async_operation() {
        let client = OtlpClient::new("http://localhost:4317");
        let result = client.connect().await;
        assert!(result.is_ok());
    }
}
```

### Test Coverage

- Aim for >80% code coverage
- Test happy paths and error cases
- Include integration tests
- Add benchmark tests for critical paths

### Running Tests

```bash
# Run all tests
cargo test --workspace

# Run specific test
cargo test test_client_creation

# Run with output
cargo test -- --nocapture

# Run integration tests only
cargo test --test integration_test
```

---

## 📚 Documentation Guidelines

### Code Documentation

```rust
/// Brief description of the function.
///
/// More detailed explanation if needed. Can span
/// multiple lines and include markdown.
///
/// # Arguments
///
/// * `endpoint` - The OTLP endpoint URL
/// * `config` - Configuration options
///
/// # Returns
///
/// Returns a `Result` containing the client or an error.
///
/// # Examples
///
/// ```
/// use otlp::OtlpClient;
///
/// let client = OtlpClient::new("http://localhost:4317");
/// ```
///
/// # Errors
///
/// Returns `OtlpError::ConnectionError` if connection fails.
pub fn new(endpoint: &str, config: ClientConfig) -> Result<Self, OtlpError> {
    // Implementation
}
```

### Documentation Files

- Use clear, concise language
- Include code examples
- Add diagrams where helpful
- Keep formatting consistent

### Example Code

- All examples must compile and run
- Include necessary imports
- Show realistic use cases
- Add comments explaining key points

---

## 🔄 Pull Request Process

### Before Submitting

1. **Update your branch**:

   ```bash
   git fetch upstream
   git rebase upstream/main
   ```

2. **Run checks**:

   ```bash
   cargo fmt --all
   cargo clippy --all-targets --all-features
   cargo test --workspace
   ```

3. **Update documentation**:
   - Update relevant docs
   - Add examples if needed
   - Update CHANGELOG.md

### Submitting the PR

1. **Push to your fork**:

   ```bash
   git push origin feature/your-feature-name
   ```

2. **Create Pull Request** on GitHub

3. **Fill out PR template** completely

4. **Link related issues** using keywords:
   - `Fixes #123`
   - `Closes #456`
   - `Relates to #789`

### PR Review Process

1. **Automated checks** must pass
2. **Code review** by maintainers
3. **Address feedback** promptly
4. **Approval** from at least one maintainer
5. **Merge** by maintainer

### After Merge

- Your PR will be included in the next release
- You'll be added to contributors list
- Consider joining as a regular contributor!

---

## 🎓 Development Tips

### Useful Commands

```bash
# Format code
cargo fmt --all

# Check for common mistakes
cargo clippy --all-targets --all-features

# Build documentation
cargo doc --all-features --no-deps --open

# Run benchmarks
cargo bench

# Check for outdated dependencies
cargo outdated
```

### IDE Setup

**VS Code**:

- Install rust-analyzer extension
- Install CodeLLDB for debugging
- Configure auto-format on save

**IntelliJ IDEA**:

- Install Rust plugin
- Enable format on save
- Configure clippy integration

---

## 🌐 Community

### Communication Channels

- **GitHub Issues**: Bug reports and feature requests
- **GitHub Discussions**: General questions and discussions
- **Discord** (if available): Real-time chat
- **Twitter/X**: Announcements and updates

### Getting Help

- Check existing [documentation](docs/)
- Search [existing issues](https://github.com/OWNER/OTLP_rust/issues)
- Ask in [GitHub Discussions](https://github.com/OWNER/OTLP_rust/discussions)
- Join our Discord server (if available)

### Recognition

We recognize contributors in several ways:

- Listed in CONTRIBUTORS.md
- Mentioned in release notes
- Showcased in project README
- Invited to join core team (for regular contributors)

---

## 📝 Commit Message Guidelines

### Format

```text
<type>(<scope>): <subject>

<body>

<footer>
```

### Types

- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `style`: Code style changes (formatting)
- `refactor`: Code refactoring
- `test`: Test updates
- `chore`: Build/tooling changes

### Examples

```text
feat(client): add retry mechanism

Implement exponential backoff retry logic for failed requests.
Configurable max attempts and initial delay.

Closes #123
```

```text
fix(reliability): correct error context propagation

Error context was not being properly propagated through
the async call chain.

Fixes #456
```

---

## 🏆 Recognition

### Hall of Fame

Top contributors will be recognized in our README and annual reports.

### Rewards

- Recognition in release notes
- Invitation to maintainer team
- Direct influence on project direction
- Community reputation

---

## 📋 Checklist for First-Time Contributors

- [ ] Read this guide completely
- [ ] Set up development environment
- [ ] Build and test the project locally
- [ ] Find a "good first issue"
- [ ] Ask questions if unclear
- [ ] Submit your first PR
- [ ] Join our community channels

---

## 🙏 Thank You

Every contribution, no matter how small, is valuable. Thank you for making OTLP Rust better!

**Happy Contributing! 🚀**-

---

*Last Updated: 2025-10-20*-
