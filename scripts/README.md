# 脚本目录说明

**最后更新**: 2025年1月

---

## 📋 目录

本目录包含项目构建、测试、部署和维护相关的脚本。

---

## 🚀 快速使用

### 构建和测试

#### 完整构建检查

```bash
# Linux/macOS
./scripts/build_all.sh

# Windows PowerShell
.\scripts\build_all.ps1
```

#### 测试覆盖率

```bash
# Linux/macOS
./scripts/test_with_coverage.sh

# Windows PowerShell
.\scripts\test_with_coverage.ps1
```

---

## 📁 脚本分类

### 构建脚本

- `build_all.sh` / `build_all.ps1` - 完整构建和检查
  - 代码格式化检查
  - Clippy 检查
  - 编译检查
  - 测试运行
  - 文档检查

### 测试脚本

- `test_with_coverage.sh` / `test_with_coverage.ps1` - 测试覆盖率
  - 运行所有测试
  - 生成覆盖率报告 (LCOV 和 HTML)
  - 需要 cargo-llvm-cov 工具

### 其他脚本

- 查看 `scripts/` 目录获取更多脚本

---

## 🔧 工具要求

### 必需工具

- `cargo` - Rust 包管理器
- `rustc` - Rust 编译器

### 可选工具

- `cargo-llvm-cov` - 覆盖率报告 (用于覆盖率脚本)

  ```bash
  cargo install cargo-llvm-cov
  ```

---

## 📝 使用说明

### Linux/macOS

```bash
# 给脚本添加执行权限
chmod +x scripts/*.sh

# 运行脚本
./scripts/build_all.sh
```

### Windows PowerShell

```powershell
# 直接运行 PowerShell 脚本
.\scripts\build_all.ps1

# 如果遇到执行策略问题，运行:
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

---

## 🎯 最佳实践

1. **提交前检查**: 运行 `build_all.sh` 确保所有检查通过
2. **覆盖率检查**: 定期运行覆盖率脚本，确保测试覆盖率达标
3. **CI/CD 集成**: 这些脚本可用于 CI/CD 流水线

---

**状态**: 📊 持续更新
