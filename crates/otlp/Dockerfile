# 多阶段构建 Dockerfile for OTLP Rust Server
# 使用 Rust 1.90 和 Alpine Linux 进行优化构建

# 构建阶段
FROM rust:1.90-alpine AS builder

# 安装构建依赖
RUN apk add --no-cache \
    musl-dev \
    pkgconfig \
    openssl-dev \
    openssl-libs-static \
    libc-dev \
    gcc \
    git

# 设置工作目录
WORKDIR /app

# 复制 Cargo 文件
COPY Cargo.toml Cargo.lock ./

# 创建虚拟项目以缓存依赖
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src

# 复制源代码
COPY src ./src
COPY examples ./examples
COPY tests ./tests

# 构建项目
RUN cargo build --release --target x86_64-unknown-linux-musl

# 运行时阶段
FROM alpine:3.18

# 安装运行时依赖
RUN apk add --no-cache \
    ca-certificates \
    tzdata \
    libgcc \
    && rm -rf /var/cache/apk/*

# 创建非 root 用户
RUN addgroup -g 1000 otlp && \
    adduser -D -s /bin/sh -u 1000 -G otlp otlp

# 设置工作目录
WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/target/x86_64-unknown-linux-musl/release/otlp-server /app/otlp-server

# 复制配置文件
COPY k8s/otlp-config.yaml /app/config.yaml

# 创建必要的目录
RUN mkdir -p /app/logs /app/tmp && \
    chown -R otlp:otlp /app

# 切换到非 root 用户
USER otlp

# 暴露端口
EXPOSE 4317 4318 8080 8081

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:8081/health || exit 1

# 设置环境变量
ENV RUST_LOG=info
ENV RUST_BACKTRACE=1
ENV OTLP_CONFIG_PATH=/app/config.yaml

# 启动命令
CMD ["/app/otlp-server"]
