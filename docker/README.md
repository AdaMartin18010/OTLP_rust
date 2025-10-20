# Docker 配置

本目录包含项目的 Docker 配置文件。

---

## 📁 文件说明

| 文件 | 说明 | 用途 |
|------|------|------|
| `Dockerfile` | 开发环境配置 | 用于本地开发和测试 |
| `Dockerfile.production` | 生产环境配置 | 用于生产部署 |

---

## 🚀 快速开始

### 构建开发环境镜像

```bash
docker build -f docker/Dockerfile -t otlp-rust:dev .
```

### 构建生产环境镜像

```bash
docker build -f docker/Dockerfile.production -t otlp-rust:latest .
```

### 运行容器

```bash
# 开发环境
docker run -it --rm -v $(pwd):/workspace otlp-rust:dev

# 生产环境
docker run -d -p 8080:8080 otlp-rust:latest
```

---

## 🔧 开发环境 (Dockerfile)

**特性**：

- 包含完整的开发工具链
- 支持热重载
- 挂载源代码目录
- 包含测试和调试工具

**适用场景**：

- 本地开发
- 集成测试
- CI/CD 构建

---

## 🚀 生产环境 (Dockerfile.production)

**特性**：

- 多阶段构建，最小化镜像体积
- 只包含运行时必需文件
- 优化的性能配置
- 安全加固

**适用场景**：

- 生产部署
- Kubernetes/Docker Swarm
- 云平台部署

---

## 📊 镜像对比

| 特性 | 开发环境 | 生产环境 |
|------|----------|----------|
| 镜像大小 | ~2GB | ~50MB |
| 构建时间 | 快 | 慢（优化） |
| 包含工具 | 完整 | 最小 |
| 安全性 | 一般 | 高 |

---

## 🔍 最佳实践

### 1. 使用 .dockerignore

确保 `.dockerignore` 文件包含：

```text
target/
.git/
*.md
docs/
tests/
benchmarks/
```

### 2. 多阶段构建

生产环境使用多阶段构建：

```dockerfile
# 构建阶段
FROM rust:1.90 AS builder
# ... 构建

# 运行阶段
FROM debian:bookworm-slim
COPY --from=builder /app/target/release/otlp /usr/local/bin/
```

### 3. 健康检查

添加健康检查：

```dockerfile
HEALTHCHECK --interval=30s --timeout=3s \
  CMD curl -f http://localhost:8080/health || exit 1
```

---

## 🛠️ 常见问题

### Q: 如何加速构建？

A: 使用 Docker BuildKit 和缓存：

```bash
DOCKER_BUILDKIT=1 docker build --cache-from otlp-rust:dev -f docker/Dockerfile .
```

### Q: 如何调试容器？

A: 使用交互模式：

```bash
docker run -it --entrypoint /bin/bash otlp-rust:dev
```

### Q: 如何优化镜像大小？

A:

1. 使用多阶段构建
2. 使用 alpine 或 distroless 基础镜像
3. 清理缓存：`RUN cargo build --release && rm -rf target/debug`

---

## 📝 维护说明

- **更新频率**: 跟随 Rust 版本更新
- **测试要求**: 每次修改后需测试构建
- **兼容性**: 保持与 Cargo.toml 中的 Rust 版本一致

---

## 🔗 相关资源

- [Docker 官方文档](https://docs.docker.com/)
- [Rust Docker 最佳实践](https://docs.docker.com/language/rust/)
- [项目主文档](../README.md)
