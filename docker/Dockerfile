# 多阶段构建 - 构建阶段
FROM rust:1.90 as builder

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

# 构建应用
RUN cargo build --release --bin otlp

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
COPY --from=builder /app/target/release/otlp /usr/local/bin/otlp

# 创建配置目录
RUN mkdir -p /app/config && chown -R otlp:otlp /app

# 复制配置文件
COPY --chown=otlp:otlp otlp/config/ /app/config/

# 切换到非root用户
USER otlp

# 暴露端口
EXPOSE 8080 4317 4318

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# 设置环境变量
ENV RUST_LOG=info
ENV OTLP_ENDPOINT=http://localhost:4317

# 启动命令
CMD ["otlp"]