# 多阶段构建Dockerfile for OTLP Rust
# 使用Rust 1.90官方镜像

# 构建阶段
FROM rust:1.90-slim as builder

# 设置工作目录
WORKDIR /app

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 复制Cargo文件
COPY Cargo.toml Cargo.lock ./

# 复制源代码
COPY otlp/ ./otlp/
COPY examples/ ./examples/

# 构建发布版本
RUN cargo build --release --package otlp

# 运行阶段
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN groupadd -r otlp && useradd -r -g otlp otlp

# 设置工作目录
WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/target/release/otlp /app/otlp

# 复制配置文件
COPY otlp/deploy/helm/otlp/config.yaml /app/config.yaml

# 设置权限
RUN chown -R otlp:otlp /app
USER otlp

# 暴露端口
EXPOSE 8080 4317 4318

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# 启动命令
CMD ["./otlp", "--config", "config.yaml"]
