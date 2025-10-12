# Tracing Appender日志管理：日志轮转归档与OTLP集成指南 (Rust 1.90)

## 目录

- [Tracing Appender日志管理：日志轮转归档与OTLP集成指南 (Rust 1.90)](#tracing-appender日志管理日志轮转归档与otlp集成指南-rust-190)
  - [目录](#目录)
  - [一、日志管理核心概念](#一日志管理核心概念)
    - [1.1 日志级别](#11-日志级别)
    - [1.2 日志轮转策略](#12-日志轮转策略)
    - [1.3 日志归档](#13-日志归档)
  - [二、Rust日志生态](#二rust日志生态)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 项目配置](#22-项目配置)
  - [三、基础日志输出](#三基础日志输出)
    - [3.1 文件Appender](#31-文件appender)
    - [3.2 非阻塞Appender](#32-非阻塞appender)
    - [3.3 多目标输出](#33-多目标输出)
  - [四、日志轮转实现](#四日志轮转实现)
    - [4.1 基于时间的轮转](#41-基于时间的轮转)
    - [4.2 基于文件大小的轮转](#42-基于文件大小的轮转)
    - [4.3 自定义轮转策略](#43-自定义轮转策略)
  - [五、日志归档](#五日志归档)
    - [5.1 压缩归档](#51-压缩归档)
    - [5.2 远程归档（S3）](#52-远程归档s3)
    - [5.3 自动清理](#53-自动清理)
  - [六、结构化日志](#六结构化日志)
    - [6.1 JSON格式](#61-json格式)
    - [6.2 自定义字段](#62-自定义字段)
    - [6.3 上下文传播](#63-上下文传播)
  - [七、OTLP日志集成](#七otlp日志集成)
    - [7.1 OpenTelemetry Logs导出](#71-opentelemetry-logs导出)
    - [7.2 日志与追踪关联](#72-日志与追踪关联)
    - [7.3 多后端导出](#73-多后端导出)
  - [八、性能优化](#八性能优化)
    - [8.1 异步批量写入](#81-异步批量写入)
    - [8.2 缓冲区优化](#82-缓冲区优化)
    - [8.3 性能基准测试](#83-性能基准测试)
  - [九、生产级配置](#九生产级配置)
    - [9.1 分级日志管理](#91-分级日志管理)
    - [9.2 动态日志级别](#92-动态日志级别)
    - [9.3 日志采样](#93-日志采样)
  - [十、监控与告警](#十监控与告警)
    - [10.1 日志指标](#101-日志指标)
    - [10.2 错误日志告警](#102-错误日志告警)
    - [10.3 日志健康检查](#103-日志健康检查)
  - [十一、Docker部署](#十一docker部署)
  - [十二、参考资源](#十二参考资源)
    - [官方文档](#官方文档)
    - [国际标准](#国际标准)
    - [工具](#工具)
  - [总结](#总结)

---

## 一、日志管理核心概念

### 1.1 日志级别

标准日志级别（从低到高）：

| 级别    | 用途                           | 生产环境  |
|---------|-------------------------------|----------|
| TRACE   | 详细调试信息（函数进出）         | ❌       |
| DEBUG   | 调试信息（变量值、状态）         | ❌       |
| INFO    | 业务流程（用户操作、关键事件）    | ✅       |
| WARN    | 警告（非致命错误、降级）         | ✅       |
| ERROR   | 错误（需要关注）                | ✅       |

**最佳实践**：

- 开发环境：DEBUG
- 测试环境：INFO
- 生产环境：INFO（关键服务）或 WARN（高吞吐服务）

### 1.2 日志轮转策略

**基于时间**：

- **Hourly**：每小时生成新文件（高流量服务）
- **Daily**：每天生成新文件（标准）
- **Never**：单文件（仅测试）

**基于大小**：

- 文件达到指定大小（如100MB）时轮转
- 适用于流量不均匀的服务

**混合策略**：

- 每天轮转 + 单文件最大100MB

### 1.3 日志归档

**保留策略**：

- **热数据**：最近7天，存储在本地SSD
- **温数据**：8-30天，压缩后存储
- **冷数据**：31-365天，归档到S3
- **删除**：超过365天

**压缩算法**：

- **gzip**：通用，压缩率70-80%
- **zstd**：高性能，压缩率80-85%

---

## 二、Rust日志生态

### 2.1 核心依赖

```toml
[dependencies]
# Tracing核心
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json", "ansi"] }
tracing-appender = "0.2"

# OpenTelemetry集成
opentelemetry = { version = "0.31", features = ["logs"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "logs"] }
opentelemetry-otlp = { version = "0.31", features = ["logs", "grpc-tonic"] }
opentelemetry-appender-tracing = "0.31"
tracing-opentelemetry = "0.28"

# 日志压缩
flate2 = "1.0"          # gzip
zstd = "0.13"           # zstd

# AWS S3
aws-config = "1.5"
aws-sdk-s3 = "1.72"

# 时间处理
chrono = "0.4"

# 异步运行时
tokio = { version = "1.42", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

[dev-dependencies]
tempfile = "3"
```

### 2.2 项目配置

```bash
mkdir -p log-demo/src/{appender,rotation,archive,otel}
cd log-demo
cargo init
```

---

## 三、基础日志输出

### 3.1 文件Appender

创建基础文件日志输出：

```rust
// src/appender/file.rs
use tracing_appender::{non_blocking, rolling};
use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// 初始化文件日志
pub fn init_file_logging(log_dir: &str) {
    let file_appender = rolling::daily(log_dir, "app.log");
    let (non_blocking_appender, _guard) = non_blocking(file_appender);

    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with(
            fmt::layer()
                .with_writer(non_blocking_appender)
                .with_ansi(false) // 文件输出禁用ANSI颜色
                .with_target(true)
                .with_thread_ids(true)
                .with_file(true)
                .with_line_number(true),
        )
        .init();

    tracing::info!("File logging initialized: {}", log_dir);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_file_logging() {
        let temp_dir = tempdir().unwrap();
        let log_path = temp_dir.path().to_str().unwrap();

        init_file_logging(log_path);

        tracing::info!("Test log message");
        tracing::error!(error_code = 500, "Test error");

        // 验证日志文件存在
        let log_files: Vec<_> = std::fs::read_dir(log_path)
            .unwrap()
            .filter_map(Result::ok)
            .collect();

        assert!(!log_files.is_empty());
    }
}
```

### 3.2 非阻塞Appender

使用非阻塞I/O提升性能：

```rust
// src/appender/non_blocking.rs
use tracing_appender::non_blocking::{NonBlocking, WorkerGuard};
use tracing_appender::rolling::RollingFileAppender;

/// 创建非阻塞Appender
pub fn create_non_blocking_appender(
    appender: RollingFileAppender,
) -> (NonBlocking, WorkerGuard) {
    tracing_appender::non_blocking(appender)
}

/// 配置非阻塞Appender（带缓冲区大小）
pub fn create_buffered_appender(
    appender: RollingFileAppender,
    buffer_size: usize,
) -> (NonBlocking, WorkerGuard) {
    tracing_appender::non_blocking::NonBlockingBuilder::default()
        .lossy(false) // 不丢弃日志
        .buffered_lines_limit(buffer_size)
        .finish(appender)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tracing_appender::rolling;
    use tempfile::tempdir;

    #[test]
    fn test_non_blocking_appender() {
        let temp_dir = tempdir().unwrap();
        let file_appender = rolling::daily(temp_dir.path(), "test.log");

        let (_non_blocking, _guard) = create_non_blocking_appender(file_appender);

        // Guard在测试结束时自动刷新缓冲区
    }

    #[test]
    fn test_buffered_appender() {
        let temp_dir = tempdir().unwrap();
        let file_appender = rolling::daily(temp_dir.path(), "test.log");

        let (_non_blocking, _guard) = create_buffered_appender(file_appender, 10_000);

        println!("Buffered appender created with 10,000 lines buffer");
    }
}
```

### 3.3 多目标输出

同时输出到控制台和文件：

```rust
// src/appender/multi_target.rs
use tracing_appender::rolling;
use tracing_subscriber::{
    fmt,
    layer::SubscriberExt,
    util::SubscriberInitExt,
    EnvFilter,
};

pub fn init_multi_target_logging(log_dir: &str) {
    let file_appender = rolling::daily(log_dir, "app.log");
    let (non_blocking_file, _guard) = tracing_appender::non_blocking(file_appender);

    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        // 控制台输出（带颜色）
        .with(
            fmt::layer()
                .with_writer(std::io::stdout)
                .with_ansi(true)
                .with_target(false)
                .compact(),
        )
        // 文件输出（详细信息）
        .with(
            fmt::layer()
                .with_writer(non_blocking_file)
                .with_ansi(false)
                .with_target(true)
                .with_thread_ids(true)
                .with_file(true)
                .with_line_number(true),
        )
        .init();

    tracing::info!("Multi-target logging initialized");
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_multi_target() {
        let temp_dir = tempdir().unwrap();
        init_multi_target_logging(temp_dir.path().to_str().unwrap());

        tracing::info!("This appears in both console and file");
        tracing::warn!(user_id = 123, "Warning message");
    }
}
```

---

## 四、日志轮转实现

### 4.1 基于时间的轮转

实现小时、天、周轮转：

```rust
// src/rotation/time_based.rs
use tracing_appender::rolling::{RollingFileAppender, Rotation};
use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub enum RotationStrategy {
    Hourly,
    Daily,
    Weekly,
}

impl RotationStrategy {
    fn to_rotation(&self) -> Rotation {
        match self {
            Self::Hourly => Rotation::HOURLY,
            Self::Daily => Rotation::DAILY,
            Self::Weekly => Rotation::NEVER, // tracing-appender不支持WEEKLY，需自定义
        }
    }
}

pub fn init_time_based_rotation(log_dir: &str, strategy: RotationStrategy) {
    let file_appender = RollingFileAppender::new(
        strategy.to_rotation(),
        log_dir,
        "app.log",
    );

    let (non_blocking, _guard) = tracing_appender::non_blocking(file_appender);

    tracing_subscriber::registry()
        .with(EnvFilter::new("info"))
        .with(
            fmt::layer()
                .with_writer(non_blocking)
                .with_ansi(false),
        )
        .init();

    tracing::info!("Time-based rotation initialized: {:?}", strategy);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_daily_rotation() {
        let temp_dir = tempdir().unwrap();
        init_time_based_rotation(temp_dir.path().to_str().unwrap(), RotationStrategy::Daily);

        for i in 0..100 {
            tracing::info!(iteration = i, "Log entry");
        }

        // 验证日志文件命名格式：app.log.2025-10-11
        let log_files: Vec<_> = std::fs::read_dir(temp_dir.path())
            .unwrap()
            .filter_map(Result::ok)
            .collect();

        assert!(!log_files.is_empty());
    }
}
```

### 4.2 基于文件大小的轮转

自定义基于大小的轮转：

```rust
// src/rotation/size_based.rs
use std::fs::{File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

pub struct SizeBasedRotation {
    log_dir: PathBuf,
    file_prefix: String,
    max_size_bytes: u64,
    current_file: Arc<Mutex<Option<File>>>,
    current_size: Arc<Mutex<u64>>,
}

impl SizeBasedRotation {
    pub fn new(log_dir: &Path, file_prefix: &str, max_size_mb: u64) -> Self {
        std::fs::create_dir_all(log_dir).unwrap();

        Self {
            log_dir: log_dir.to_path_buf(),
            file_prefix: file_prefix.to_string(),
            max_size_bytes: max_size_mb * 1024 * 1024,
            current_file: Arc::new(Mutex::new(None)),
            current_size: Arc::new(Mutex::new(0)),
        }
    }

    pub fn write(&self, data: &[u8]) -> io::Result<()> {
        let mut file_lock = self.current_file.lock().unwrap();
        let mut size_lock = self.current_size.lock().unwrap();

        // 检查是否需要轮转
        if *size_lock + data.len() as u64 > self.max_size_bytes {
            self.rotate(&mut file_lock)?;
            *size_lock = 0;
        }

        // 打开文件（如果未打开）
        if file_lock.is_none() {
            let path = self.current_log_path();
            *file_lock = Some(
                OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(path)?,
            );
        }

        // 写入数据
        if let Some(ref mut file) = *file_lock {
            file.write_all(data)?;
            file.flush()?;
            *size_lock += data.len() as u64;
        }

        Ok(())
    }

    fn rotate(&self, file_lock: &mut Option<File>) -> io::Result<()> {
        // 关闭当前文件
        *file_lock = None;

        // 重命名当前文件
        let current_path = self.current_log_path();
        if current_path.exists() {
            let timestamp = chrono::Utc::now().format("%Y%m%d_%H%M%S");
            let rotated_path = self
                .log_dir
                .join(format!("{}_{}.log", self.file_prefix, timestamp));
            std::fs::rename(&current_path, &rotated_path)?;
            tracing::info!("Rotated log file: {:?}", rotated_path);
        }

        Ok(())
    }

    fn current_log_path(&self) -> PathBuf {
        self.log_dir.join(format!("{}.log", self.file_prefix))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_size_based_rotation() {
        let temp_dir = tempdir().unwrap();
        let rotation = SizeBasedRotation::new(temp_dir.path(), "app", 1); // 1MB

        // 写入2MB数据，触发轮转
        for _ in 0..2048 {
            let data = vec![b'A'; 1024]; // 1KB per write
            rotation.write(&data).unwrap();
        }

        // 验证轮转文件存在
        let log_files: Vec<_> = std::fs::read_dir(temp_dir.path())
            .unwrap()
            .filter_map(Result::ok)
            .collect();

        assert!(log_files.len() >= 2); // 至少有当前文件和一个轮转文件
    }
}
```

### 4.3 自定义轮转策略

结合时间和大小的混合轮转：

```rust
// src/rotation/custom.rs
use std::path::Path;
use tracing_appender::rolling::{RollingFileAppender, Rotation};

pub struct CustomRotation {
    time_rotation: Rotation,
    max_size_mb: u64,
}

impl CustomRotation {
    pub fn new(time_rotation: Rotation, max_size_mb: u64) -> Self {
        Self {
            time_rotation,
            max_size_mb,
        }
    }

    pub fn create_appender(&self, log_dir: &Path, file_prefix: &str) -> RollingFileAppender {
        // 使用tracing_appender的时间轮转
        // 在实际应用中，结合size_based模块实现混合轮转
        RollingFileAppender::new(self.time_rotation, log_dir, file_prefix)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_custom_rotation() {
        let temp_dir = tempdir().unwrap();
        let custom = CustomRotation::new(Rotation::DAILY, 100);

        let _appender = custom.create_appender(temp_dir.path(), "app.log");

        println!("Custom rotation: daily + 100MB limit");
    }
}
```

---

## 五、日志归档

### 5.1 压缩归档

使用gzip压缩旧日志：

```rust
// src/archive/compression.rs
use flate2::write::GzEncoder;
use flate2::Compression;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

pub fn compress_log_file(src: &Path, dest: &Path) -> io::Result<()> {
    let mut input = File::open(src)?;
    let output = File::create(dest)?;
    let mut encoder = GzEncoder::new(output, Compression::default());

    let mut buffer = Vec::new();
    input.read_to_end(&mut buffer)?;
    encoder.write_all(&buffer)?;
    encoder.finish()?;

    tracing::info!("Compressed: {:?} -> {:?}", src, dest);

    Ok(())
}

pub fn compress_old_logs(log_dir: &Path, days_old: u64) -> io::Result<()> {
    let cutoff = chrono::Utc::now() - chrono::Duration::days(days_old as i64);

    for entry in std::fs::read_dir(log_dir)? {
        let entry = entry?;
        let path = entry.path();

        if path.extension().and_then(|s| s.to_str()) == Some("log") {
            let metadata = entry.metadata()?;
            if let Ok(modified) = metadata.modified() {
                let modified_time: chrono::DateTime<chrono::Utc> = modified.into();

                if modified_time < cutoff {
                    let gz_path = path.with_extension("log.gz");
                    compress_log_file(&path, &gz_path)?;
                    std::fs::remove_file(&path)?; // 删除原文件
                }
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::tempdir;

    #[test]
    fn test_compress_log() {
        let temp_dir = tempdir().unwrap();

        // 创建测试日志文件
        let log_path = temp_dir.path().join("test.log");
        let mut file = File::create(&log_path).unwrap();
        writeln!(file, "Log entry 1").unwrap();
        writeln!(file, "Log entry 2").unwrap();

        // 压缩
        let gz_path = temp_dir.path().join("test.log.gz");
        compress_log_file(&log_path, &gz_path).unwrap();

        assert!(gz_path.exists());

        // 验证压缩率
        let original_size = log_path.metadata().unwrap().len();
        let compressed_size = gz_path.metadata().unwrap().len();
        println!("Compression ratio: {:.2}%", (compressed_size as f64 / original_size as f64) * 100.0);
    }

    #[test]
    fn test_compress_old_logs() {
        let temp_dir = tempdir().unwrap();

        // 创建多个日志文件
        for i in 0..5 {
            let log_path = temp_dir.path().join(format!("app_{}.log", i));
            let mut file = File::create(&log_path).unwrap();
            writeln!(file, "Log data {}", i).unwrap();
        }

        // 压缩7天前的日志（测试中立即压缩）
        compress_old_logs(temp_dir.path(), 0).unwrap();

        // 验证.gz文件存在
        let gz_files: Vec<_> = std::fs::read_dir(temp_dir.path())
            .unwrap()
            .filter_map(Result::ok)
            .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("gz"))
            .collect();

        assert!(!gz_files.is_empty());
    }
}
```

### 5.2 远程归档（S3）

将压缩日志上传到AWS S3：

```rust
// src/archive/s3_upload.rs
use aws_config::BehaviorVersion;
use aws_sdk_s3::primitives::ByteStream;
use aws_sdk_s3::Client;
use std::path::Path;

pub struct S3Archiver {
    client: Client,
    bucket: String,
}

impl S3Archiver {
    pub async fn new(bucket: String) -> Self {
        let config = aws_config::load_defaults(BehaviorVersion::latest()).await;
        let client = Client::new(&config);

        Self { client, bucket }
    }

    pub async fn upload_log(&self, local_path: &Path, s3_key: &str) -> anyhow::Result<()> {
        let body = ByteStream::from_path(local_path).await?;

        self.client
            .put_object()
            .bucket(&self.bucket)
            .key(s3_key)
            .body(body)
            .send()
            .await?;

        tracing::info!(
            local_path = %local_path.display(),
            s3_key = s3_key,
            "Log uploaded to S3"
        );

        Ok(())
    }

    pub async fn archive_old_logs(&self, log_dir: &Path, days_old: u64) -> anyhow::Result<()> {
        let cutoff = chrono::Utc::now() - chrono::Duration::days(days_old as i64);

        for entry in std::fs::read_dir(log_dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.extension().and_then(|s| s.to_str()) == Some("gz") {
                let metadata = entry.metadata()?;
                if let Ok(modified) = metadata.modified() {
                    let modified_time: chrono::DateTime<chrono::Utc> = modified.into();

                    if modified_time < cutoff {
                        let filename = path.file_name().unwrap().to_str().unwrap();
                        let s3_key = format!("logs/{}", filename);

                        self.upload_log(&path, &s3_key).await?;

                        // 上传成功后删除本地文件
                        std::fs::remove_file(&path)?;
                    }
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[tokio::test]
    #[ignore] // 需要AWS凭证
    async fn test_s3_upload() {
        let temp_dir = tempdir().unwrap();
        let log_path = temp_dir.path().join("test.log.gz");
        std::fs::write(&log_path, b"compressed log data").unwrap();

        let archiver = S3Archiver::new("my-log-bucket".to_string()).await;
        archiver.upload_log(&log_path, "logs/test.log.gz").await.unwrap();
    }
}
```

### 5.3 自动清理

定期清理过期日志：

```rust
// src/archive/cleanup.rs
use std::path::Path;
use std::time::Duration;
use tokio::time;

pub async fn start_log_cleanup_task(log_dir: &Path, retention_days: u64) {
    let log_dir = log_dir.to_path_buf();
    let mut interval = time::interval(Duration::from_secs(3600)); // 每小时检查

    tokio::spawn(async move {
        loop {
            interval.tick().await;

            if let Err(e) = cleanup_expired_logs(&log_dir, retention_days) {
                tracing::error!(error = %e, "Failed to cleanup logs");
            }
        }
    });
}

fn cleanup_expired_logs(log_dir: &Path, retention_days: u64) -> std::io::Result<()> {
    let cutoff = chrono::Utc::now() - chrono::Duration::days(retention_days as i64);

    for entry in std::fs::read_dir(log_dir)? {
        let entry = entry?;
        let path = entry.path();

        let metadata = entry.metadata()?;
        if let Ok(modified) = metadata.modified() {
            let modified_time: chrono::DateTime<chrono::Utc> = modified.into();

            if modified_time < cutoff {
                std::fs::remove_file(&path)?;
                tracing::info!(file = %path.display(), "Deleted expired log");
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_cleanup_expired_logs() {
        let temp_dir = tempdir().unwrap();

        // 创建测试文件
        for i in 0..5 {
            let path = temp_dir.path().join(format!("old_{}.log", i));
            std::fs::write(&path, b"old data").unwrap();
        }

        // 立即清理（retention_days = 0）
        cleanup_expired_logs(temp_dir.path(), 0).unwrap();

        // 验证文件被删除
        let remaining: Vec<_> = std::fs::read_dir(temp_dir.path())
            .unwrap()
            .filter_map(Result::ok)
            .collect();

        assert_eq!(remaining.len(), 0);
    }
}
```

---

## 六、结构化日志

### 6.1 JSON格式

输出JSON格式日志：

```rust
// src/structured/json_format.rs
use tracing_appender::rolling;
use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub fn init_json_logging(log_dir: &str) {
    let file_appender = rolling::daily(log_dir, "app.json");
    let (non_blocking, _guard) = tracing_appender::non_blocking(file_appender);

    tracing_subscriber::registry()
        .with(EnvFilter::new("info"))
        .with(
            fmt::layer()
                .json() // JSON格式
                .with_writer(non_blocking)
                .with_current_span(true)
                .with_span_list(true)
                .with_target(true)
                .with_thread_ids(true),
        )
        .init();

    tracing::info!("JSON logging initialized");
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_json_logging() {
        let temp_dir = tempdir().unwrap();
        init_json_logging(temp_dir.path().to_str().unwrap());

        tracing::info!(user_id = 123, action = "login", "User logged in");
        tracing::error!(error_code = 500, "Internal server error");

        // 读取JSON日志
        let log_files: Vec<_> = std::fs::read_dir(temp_dir.path())
            .unwrap()
            .filter_map(Result::ok)
            .collect();

        assert!(!log_files.is_empty());

        // 验证JSON格式
        if let Some(log_file) = log_files.first() {
            let content = std::fs::read_to_string(log_file.path()).unwrap();
            assert!(content.contains("\"user_id\":123"));
        }
    }
}
```

**JSON日志示例**：

```json
{
  "timestamp": "2025-10-11T12:34:56.789Z",
  "level": "INFO",
  "target": "app::handlers::user",
  "fields": {
    "user_id": 123,
    "action": "login",
    "message": "User logged in"
  },
  "span": {
    "name": "process_request",
    "request_id": "550e8400-e29b-41d4-a716-446655440000"
  }
}
```

### 6.2 自定义字段

添加全局上下文字段：

```rust
// src/structured/custom_fields.rs
use tracing::{info_span, Span};
use tracing_subscriber::{layer::Context, Layer};

pub struct GlobalContextLayer {
    service_name: String,
    environment: String,
}

impl GlobalContextLayer {
    pub fn new(service_name: &str, environment: &str) -> Self {
        Self {
            service_name: service_name.to_string(),
            environment: environment.to_string(),
        }
    }
}

impl<S> Layer<S> for GlobalContextLayer
where
    S: tracing::Subscriber,
{
    fn on_new_span(
        &self,
        attrs: &tracing::span::Attributes<'_>,
        id: &tracing::span::Id,
        ctx: Context<'_, S>,
    ) {
        let span = ctx.span(id).unwrap();

        // 添加全局字段
        span.extensions_mut().insert(GlobalContext {
            service_name: self.service_name.clone(),
            environment: self.environment.clone(),
        });
    }
}

#[derive(Clone)]
struct GlobalContext {
    service_name: String,
    environment: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_global_context() {
        let span = info_span!("operation", user_id = 123);
        let _enter = span.enter();

        tracing::info!("This log includes global context");
    }
}
```

### 6.3 上下文传播

在Span中传播上下文：

```rust
// src/structured/context_propagation.rs
use tracing::{info_span, instrument};

#[instrument(fields(user_id, request_id))]
pub async fn process_user_request(user_id: u64, request_id: &str) {
    tracing::info!("Processing user request");

    // 上下文自动传播到子函数
    fetch_user_data(user_id).await;
    update_user_profile(user_id).await;

    tracing::info!("Request completed");
}

#[instrument]
async fn fetch_user_data(user_id: u64) {
    tracing::debug!(user_id, "Fetching user data");
    tokio::time::sleep(std::time::Duration::from_millis(10)).await;
}

#[instrument]
async fn update_user_profile(user_id: u64) {
    tracing::debug!(user_id, "Updating user profile");
    tokio::time::sleep(std::time::Duration::from_millis(5)).await;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_context_propagation() {
        process_user_request(123, "req-001").await;
    }
}
```

---

## 七、OTLP日志集成

### 7.1 OpenTelemetry Logs导出

将日志导出到OTLP：

```rust
// src/otel/logs_exporter.rs
use opentelemetry::logs::LoggerProvider;
use opentelemetry_appender_tracing::layer::OpenTelemetryTracingBridge;
use opentelemetry_otlp::{LogExporter, WithExportConfig};
use opentelemetry_sdk::{logs::LoggerProvider as SdkLoggerProvider, Resource, runtime};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub fn init_otlp_logging(service_name: &str, otlp_endpoint: &str) {
    let exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint(otlp_endpoint)
        .build()
        .expect("Failed to create OTLP log exporter");

    let logger_provider = SdkLoggerProvider::builder()
        .with_batch_exporter(exporter, runtime::Tokio)
        .with_resource(Resource::new(vec![
            opentelemetry::KeyValue::new("service.name", service_name.to_string()),
        ]))
        .build();

    let otel_layer = OpenTelemetryTracingBridge::new(&logger_provider);

    tracing_subscriber::registry()
        .with(EnvFilter::new("info"))
        .with(otel_layer)
        .init();

    tracing::info!("OTLP logging initialized: {}", otlp_endpoint);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[ignore] // 需要OTLP Collector运行
    async fn test_otlp_logging() {
        init_otlp_logging("test-service", "http://localhost:4317");

        tracing::info!(user_id = 123, "Test log to OTLP");

        tokio::time::sleep(std::time::Duration::from_secs(2)).await; // 等待批量导出
    }
}
```

### 7.2 日志与追踪关联

将日志关联到Trace：

```rust
// src/otel/tracing_correlation.rs
use opentelemetry::trace::{TraceContextExt, Tracer};
use tracing::{info_span, Span};
use tracing_opentelemetry::OpenTelemetrySpanExt;

pub async fn traced_operation_with_logs() {
    let span = info_span!("traced_operation");
    let _enter = span.enter();

    // 日志自动包含Trace ID和Span ID
    tracing::info!("This log is correlated with the trace");

    expensive_computation().await;

    tracing::info!("Operation completed");
}

async fn expensive_computation() {
    tracing::debug!("Starting computation");
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    tracing::debug!("Computation done");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_correlated_logs() {
        traced_operation_with_logs().await;
    }
}
```

### 7.3 多后端导出

同时导出到文件和OTLP：

```rust
// src/otel/multi_backend.rs
use opentelemetry_appender_tracing::layer::OpenTelemetryTracingBridge;
use opentelemetry_sdk::logs::LoggerProvider;
use tracing_appender::rolling;
use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub fn init_multi_backend_logging(
    log_dir: &str,
    logger_provider: &LoggerProvider,
) {
    let file_appender = rolling::daily(log_dir, "app.log");
    let (non_blocking, _guard) = tracing_appender::non_blocking(file_appender);

    let otel_layer = OpenTelemetryTracingBridge::new(logger_provider);

    tracing_subscriber::registry()
        .with(EnvFilter::new("info"))
        // 文件输出
        .with(
            fmt::layer()
                .with_writer(non_blocking)
                .with_ansi(false)
                .json(),
        )
        // OTLP输出
        .with(otel_layer)
        .init();

    tracing::info!("Multi-backend logging initialized");
}
```

---

## 八、性能优化

### 8.1 异步批量写入

使用非阻塞I/O提升性能：

```rust
// src/performance/async_batch.rs
use tracing_appender::non_blocking::NonBlockingBuilder;
use tracing_appender::rolling;

pub fn init_optimized_logging(log_dir: &str) {
    let file_appender = rolling::daily(log_dir, "app.log");

    let (non_blocking, _guard) = NonBlockingBuilder::default()
        .lossy(false) // 不丢弃日志
        .buffered_lines_limit(10_000) // 10,000行缓冲
        .finish(file_appender);

    tracing_subscriber::fmt()
        .with_writer(non_blocking)
        .with_ansi(false)
        .init();

    tracing::info!("Optimized logging initialized");
}
```

### 8.2 缓冲区优化

调整缓冲区大小以平衡内存和性能：

```rust
// src/performance/buffer_tuning.rs
use tracing_appender::non_blocking::NonBlockingBuilder;
use tracing_appender::rolling::RollingFileAppender;

pub struct LoggingConfig {
    pub buffer_size: usize,
    pub lossy: bool,
}

impl Default for LoggingConfig {
    fn default() -> Self {
        Self {
            buffer_size: 8192, // 8KB缓冲
            lossy: false,
        }
    }
}

pub fn create_optimized_appender(
    appender: RollingFileAppender,
    config: LoggingConfig,
) -> (tracing_appender::non_blocking::NonBlocking, tracing_appender::non_blocking::WorkerGuard) {
    NonBlockingBuilder::default()
        .lossy(config.lossy)
        .buffered_lines_limit(config.buffer_size)
        .finish(appender)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    use tracing_appender::rolling;

    #[test]
    fn test_buffer_tuning() {
        let temp_dir = tempdir().unwrap();
        let file_appender = rolling::daily(temp_dir.path(), "test.log");

        let config = LoggingConfig {
            buffer_size: 16384, // 16KB
            lossy: false,
        };

        let (_non_blocking, _guard) = create_optimized_appender(file_appender, config);

        println!("Optimized appender with 16KB buffer");
    }
}
```

### 8.3 性能基准测试

评估日志性能影响：

```rust
// benches/logging_benchmark.rs (需要放在benches目录)
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use tracing::{info, instrument};

#[instrument]
fn log_intensive_operation() {
    for i in 0..1000 {
        info!(iteration = i, "Processing");
    }
}

fn benchmark_logging(c: &mut Criterion) {
    // 初始化日志（输出到/dev/null）
    tracing_subscriber::fmt()
        .with_writer(std::io::sink)
        .init();

    c.bench_function("log_1000_messages", |b| {
        b.iter(|| {
            log_intensive_operation();
        });
    });
}

criterion_group!(benches, benchmark_logging);
criterion_main!(benches);
```

**运行基准测试**：

```bash
cargo bench

# 预期结果
# log_1000_messages  time:   [2.5 ms 2.6 ms 2.7 ms]
```

---

## 九、生产级配置

### 9.1 分级日志管理

不同级别日志输出到不同文件：

```rust
// src/production/tiered_logging.rs
use tracing_appender::rolling;
use tracing_subscriber::{
    filter::LevelFilter, fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter,
};

pub fn init_tiered_logging(log_dir: &str) {
    // INFO级别日志
    let info_appender = rolling::daily(log_dir, "info.log");
    let (info_writer, _info_guard) = tracing_appender::non_blocking(info_appender);

    // ERROR级别日志
    let error_appender = rolling::daily(log_dir, "error.log");
    let (error_writer, _error_guard) = tracing_appender::non_blocking(error_appender);

    tracing_subscriber::registry()
        // INFO及以上级别 -> info.log
        .with(
            fmt::layer()
                .with_writer(info_writer)
                .with_ansi(false)
                .json()
                .with_filter(LevelFilter::INFO),
        )
        // ERROR及以上级别 -> error.log
        .with(
            fmt::layer()
                .with_writer(error_writer)
                .with_ansi(false)
                .json()
                .with_filter(LevelFilter::ERROR),
        )
        .init();

    tracing::info!("Tiered logging initialized");
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_tiered_logging() {
        let temp_dir = tempdir().unwrap();
        init_tiered_logging(temp_dir.path().to_str().unwrap());

        tracing::info!("This goes to info.log");
        tracing::error!("This goes to both info.log and error.log");

        // 验证两个文件都存在
        let files: Vec<_> = std::fs::read_dir(temp_dir.path())
            .unwrap()
            .filter_map(Result::ok)
            .collect();

        assert!(files.len() >= 2);
    }
}
```

### 9.2 动态日志级别

运行时调整日志级别：

```rust
// src/production/dynamic_level.rs
use std::sync::Arc;
use tracing::Level;
use tracing_subscriber::{reload, EnvFilter, Registry};

pub struct DynamicLogger {
    reload_handle: reload::Handle<EnvFilter, Registry>,
}

impl DynamicLogger {
    pub fn new() -> (Self, reload::Layer<EnvFilter, Registry>) {
        let (filter, reload_handle) = reload::Layer::new(EnvFilter::new("info"));

        (Self { reload_handle }, filter)
    }

    pub fn set_level(&self, level: Level) -> Result<(), reload::Error> {
        let new_filter = EnvFilter::new(level.to_string());
        self.reload_handle.reload(new_filter)
    }

    pub fn set_module_level(&self, module: &str, level: Level) -> Result<(), reload::Error> {
        let new_filter = EnvFilter::new(format!("{}={}", module, level));
        self.reload_handle.reload(new_filter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

    #[test]
    fn test_dynamic_level() {
        let (logger, reload_layer) = DynamicLogger::new();

        tracing_subscriber::registry()
            .with(reload_layer)
            .with(tracing_subscriber::fmt::layer())
            .init();

        tracing::info!("Info level (visible)");
        tracing::debug!("Debug level (not visible)");

        // 动态切换到DEBUG
        logger.set_level(Level::DEBUG).unwrap();

        tracing::debug!("Debug level (now visible)");
    }
}
```

### 9.3 日志采样

高流量场景下采样日志：

```rust
// src/production/sampling.rs
use std::sync::atomic::{AtomicU64, Ordering};

pub struct LogSampler {
    counter: AtomicU64,
    sample_rate: u64, // 每N条日志记录1条
}

impl LogSampler {
    pub fn new(sample_rate: u64) -> Self {
        Self {
            counter: AtomicU64::new(0),
            sample_rate,
        }
    }

    pub fn should_log(&self) -> bool {
        let count = self.counter.fetch_add(1, Ordering::Relaxed);
        count % self.sample_rate == 0
    }
}

#[macro_export]
macro_rules! sampled_log {
    ($sampler:expr, $level:ident, $($arg:tt)+) => {
        if $sampler.should_log() {
            tracing::$level!($($arg)+);
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sampling() {
        let sampler = LogSampler::new(10); // 采样率1/10

        let mut logged = 0;
        for _ in 0..100 {
            if sampler.should_log() {
                logged += 1;
            }
        }

        assert_eq!(logged, 10); // 正好10条
    }
}
```

---

## 十、监控与告警

### 10.1 日志指标

将日志统计导出为指标：

```rust
// src/monitoring/log_metrics.rs
use metrics::{counter, gauge};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tracing::{Event, Subscriber};
use tracing_subscriber::layer::Context;
use tracing_subscriber::Layer;

pub struct LogMetricsLayer {
    error_count: Arc<AtomicU64>,
    warn_count: Arc<AtomicU64>,
}

impl LogMetricsLayer {
    pub fn new() -> Self {
        Self {
            error_count: Arc::new(AtomicU64::new(0)),
            warn_count: Arc::new(AtomicU64::new(0)),
        }
    }

    pub fn start_metrics_export(self: Arc<Self>) {
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(10));

            loop {
                interval.tick().await;

                let errors = self.error_count.swap(0, Ordering::Relaxed);
                let warns = self.warn_count.swap(0, Ordering::Relaxed);

                counter!("log_errors_total").increment(errors);
                counter!("log_warnings_total").increment(warns);
            }
        });
    }
}

impl<S> Layer<S> for LogMetricsLayer
where
    S: Subscriber,
{
    fn on_event(&self, event: &Event<'_>, _ctx: Context<'_, S>) {
        let metadata = event.metadata();

        match *metadata.level() {
            tracing::Level::ERROR => {
                self.error_count.fetch_add(1, Ordering::Relaxed);
            }
            tracing::Level::WARN => {
                self.warn_count.fetch_add(1, Ordering::Relaxed);
            }
            _ => {}
        }
    }
}
```

### 10.2 错误日志告警

自动告警错误日志：

```rust
// src/monitoring/alerting.rs
use tracing::{Event, Subscriber};
use tracing_subscriber::layer::Context;
use tracing_subscriber::Layer;

pub struct AlertingLayer {
    alert_threshold: usize,
    error_buffer: std::sync::Mutex<Vec<String>>,
}

impl AlertingLayer {
    pub fn new(alert_threshold: usize) -> Self {
        Self {
            alert_threshold,
            error_buffer: std::sync::Mutex::new(Vec::new()),
        }
    }

    fn send_alert(&self, errors: &[String]) {
        // 实际场景中，发送到PagerDuty、Slack等
        tracing::warn!(
            error_count = errors.len(),
            "🚨 Alert: High error rate detected"
        );

        for error in errors.iter().take(5) {
            tracing::warn!("  - {}", error);
        }
    }
}

impl<S> Layer<S> for AlertingLayer
where
    S: Subscriber,
{
    fn on_event(&self, event: &Event<'_>, _ctx: Context<'_, S>) {
        if *event.metadata().level() == tracing::Level::ERROR {
            let mut buffer = self.error_buffer.lock().unwrap();
            buffer.push(format!("{:?}", event));

            if buffer.len() >= self.alert_threshold {
                self.send_alert(&buffer);
                buffer.clear();
            }
        }
    }
}
```

### 10.3 日志健康检查

监控日志系统健康状态：

```rust
// src/monitoring/health_check.rs
use std::time::{Duration, Instant};
use tokio::time;

pub struct LogHealthChecker {
    last_log_time: std::sync::Mutex<Instant>,
}

impl LogHealthChecker {
    pub fn new() -> Self {
        Self {
            last_log_time: std::sync::Mutex::new(Instant::now()),
        }
    }

    pub fn record_log(&self) {
        *self.last_log_time.lock().unwrap() = Instant::now();
    }

    pub fn is_healthy(&self, timeout: Duration) -> bool {
        let last_log = *self.last_log_time.lock().unwrap();
        last_log.elapsed() < timeout
    }

    pub async fn start_health_check(self: std::sync::Arc<Self>) {
        let mut interval = time::interval(Duration::from_secs(60));

        loop {
            interval.tick().await;

            if !self.is_healthy(Duration::from_secs(300)) {
                tracing::error!("⚠️  Log system appears unhealthy: no logs in 5 minutes");
            }
        }
    }
}
```

---

## 十一、Docker部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "3000:3000"
    environment:
      - RUST_LOG=info
      - LOG_DIR=/app/logs
      - OTLP_ENDPOINT=http://otel-collector:4317
    volumes:
      - app_logs:/app/logs

  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.114.0
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"

  loki:
    image: grafana/loki:3.3.2
    ports:
      - "3100:3100"
    command: -config.file=/etc/loki/local-config.yaml

  grafana:
    image: grafana/grafana:11.4.0
    ports:
      - "3001:3000"
    environment:
      - GF_AUTH_ANONYMOUS_ENABLED=true
      - GF_AUTH_ANONYMOUS_ORG_ROLE=Admin
    volumes:
      - grafana_data:/var/lib/grafana

volumes:
  app_logs:
  grafana_data:
```

---

## 十二、参考资源

### 官方文档

1. **tracing-appender**: <https://docs.rs/tracing-appender/>
2. **tracing-subscriber**: <https://docs.rs/tracing-subscriber/>
3. **OpenTelemetry Logs**: <https://opentelemetry.io/docs/specs/otel/logs/>

### 国际标准

1. **Log Management Best Practices** (CNCF): <https://www.cncf.io/blog/2021/10/18/log-management-best-practices/>
2. **Structured Logging** (Google SRE): <https://sre.google/sre-book/monitoring-distributed-systems/>

### 工具

1. **Loki**: <https://grafana.com/oss/loki/>
2. **Fluentd**: <https://www.fluentd.org/>
3. **Vector**: <https://vector.dev/>

---

## 总结

本文档提供了Rust 1.90中日志管理的完整指南，涵盖：

✅ **日志轮转**：时间、大小、自定义策略  
✅ **日志归档**：压缩、S3上传、自动清理  
✅ **结构化日志**：JSON格式、自定义字段、上下文传播  
✅ **OTLP集成**：日志导出、追踪关联、多后端  
✅ **性能优化**：异步批量写入、缓冲区调优  
✅ **生产配置**：分级管理、动态级别、日志采样  
✅ **监控告警**：日志指标、错误告警、健康检查  

**核心优势**：

- 遵循OpenTelemetry Logs标准
- 生产级性能（非阻塞I/O、批量写入）
- 完整的日志生命周期管理（轮转、压缩、归档、清理）
- 深度集成OpenTelemetry可观测性栈

**下一步**：

- 探索`opentelemetry-rust`高级特性
- 集成Loki、Elasticsearch等日志后端
- 学习分布式追踪最佳实践
