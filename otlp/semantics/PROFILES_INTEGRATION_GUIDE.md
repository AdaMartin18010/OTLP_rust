# Profiles集成完整指南

> **版本**: 1.0  
> **日期**: 2025年10月17日  
> **状态**: ✅ 完整版

---

## 📋 目录

- [第一部分：Profiles概述](#第一部分profiles概述)
- [第二部分：数据模型](#第二部分数据模型)
- [第三部分：采集方案](#第三部分采集方案)
- [第四部分：传输与存储](#第四部分传输与存储)
- [第五部分：查询与分析](#第五部分查询与分析)
- [第六部分：与Traces关联](#第六部分与traces关联)
- [第七部分：性能优化](#第七部分性能优化)
- [第八部分：最佳实践](#第八部分最佳实践)

---

## 第一部分：Profiles概述

### 1.1 什么是Profiles?

**Profiles(性能剖析)** 是OpenTelemetry的**第四支柱**,与Traces、Metrics、Logs并列,用于捕获应用程序的性能剖析数据,帮助识别性能瓶颈。

#### 四支柱对比

| 支柱 | 数据类型 | 主要用途 | 采样方式 |
|------|---------|---------|---------|
| **Traces** | 分布式追踪 | 请求路径、延迟分析 | 尾部采样、头部采样 |
| **Metrics** | 时间序列 | 趋势、容量规划 | 聚合统计 |
| **Logs** | 日志事件 | 故障排查、审计 | 全量/采样 |
| **Profiles** | 性能剖析 | CPU/内存热点、火焰图 | 连续/按需 |

#### Profiles的价值

```text
问题场景:
"服务延迟高,但Traces只显示总耗时,不知道哪个函数慢"
         ↓
Profiles提供答案:
┌──────────────────────────────────┐
│ CPU火焰图显示:                      │
│ - json.Marshal() 占用60% CPU      │
│ - 大量反射调用                      │
│ - GC频繁触发                       │
└──────────────────────────────────┘
         ↓
优化方向明确:
- 使用预编译序列化
- 减少反射
- 优化内存分配
```

### 1.2 Profiles类型

| 类型 | 说明 | 采样方式 | 适用场景 |
|------|------|---------|---------|
| **CPU Profile** | CPU使用情况 | 定时采样(100Hz) | 计算密集型分析 |
| **Heap Profile** | 内存分配 | 每N字节采样 | 内存泄漏排查 |
| **Goroutine Profile** | 协程栈 | 快照 | 协程泄漏分析 |
| **Mutex Profile** | 锁竞争 | 事件触发 | 并发瓶颈定位 |
| **Block Profile** | 阻塞操作 | 事件触发 | I/O瓶颈分析 |
| **Thread Profile** | 线程栈 | 快照 | 线程问题排查 |

### 1.3 Profiles在OTLP中的位置

```text
┌────────────────────────────────────────────┐
│        应用程序 (Instrumented App)          │
└───────────┬────────────────────────────────┘
            │
     ┌──────┴──────┐
     │   SDK集成   │
     │  - pprof    │
     │  - pyspy    │
     │  - async-   │
     │    profiler │
     └──────┬──────┘
            │
            ▼
┌────────────────────────────────────────────┐
│         OTLP Profiles Export               │
│  ┌──────────────────────────────────────┐  │
│  │ ProfilesData                         │  │
│  │  └─ ResourceProfiles                 │  │
│  │      └─ ScopeProfiles                │  │
│  │          └─ ProfileContainer         │  │
│  │              └─ Profile (pprof)      │  │
│  └──────────────────────────────────────┘  │
└────────────────┬───────────────────────────┘
                 │
                 ▼
┌────────────────────────────────────────────┐
│      OpenTelemetry Collector               │
│  - 接收OTLP Profiles                       │
│  - 与Traces关联                            │
│  - 路由到后端                              │
└────────────────┬───────────────────────────┘
                 │
                 ▼
┌────────────────────────────────────────────┐
│         后端存储                            │
│  - Pyroscope                               │
│  - Grafana Phlare                          │
│  - Datadog                                 │
└────────────────────────────────────────────┘
```

---

## 第二部分：数据模型

### 2.1 OTLP Profiles数据结构

```protobuf
// ProfilesData是顶层容器
message ProfilesData {
  repeated ResourceProfiles resource_profiles = 1;
}

// ResourceProfiles包含Resource和Profiles
message ResourceProfiles {
  opentelemetry.proto.resource.v1.Resource resource = 1;
  repeated ScopeProfiles scope_profiles = 2;
  string schema_url = 3;
}

// ScopeProfiles包含InstrumentationScope和Profiles
message ScopeProfiles {
  opentelemetry.proto.common.v1.InstrumentationScope scope = 1;
  repeated ProfileContainer profiles = 2;
  string schema_url = 3;
}

// ProfileContainer是单个Profile的容器
message ProfileContainer {
  // Profile ID
  bytes profile_id = 1;
  
  // 时间范围
  fixed64 start_time_unix_nano = 2;
  fixed64 end_time_unix_nano = 3;
  
  // 属性
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 4;
  uint32 dropped_attributes_count = 5;
  
  // 原始pprof数据
  bytes profile = 6;
}
```

### 2.2 pprof数据格式

```protobuf
// pprof格式 (Google的profiling format)
message Profile {
  // 采样类型
  repeated ValueType sample_type = 1;
  
  // 样本数据
  repeated Sample sample = 2;
  
  // 地址映射
  repeated Mapping mapping = 3;
  
  // 函数位置
  repeated Location location = 4;
  
  // 函数信息
  repeated Function function = 5;
  
  // 字符串表
  repeated string string_table = 6;
  
  // 时间
  int64 time_nanos = 9;
  int64 duration_nanos = 10;
  
  // Profile类型
  ValueType period_type = 11;
  int64 period = 12;
}

message Sample {
  repeated uint64 location_id = 1;  // 调用栈
  repeated int64 value = 2;         // 样本值
  repeated Label label = 3;         // 标签
}

message Location {
  uint64 id = 1;
  uint64 mapping_id = 2;
  uint64 address = 3;
  repeated Line line = 4;
}

message Function {
  uint64 id = 1;
  int64 name = 2;         // string_table索引
  int64 system_name = 3;
  int64 filename = 4;
  int64 start_line = 5;
}
```

### 2.3 Rust数据模型

```rust
// OTLP Profiles数据结构
use prost::Message;

#[derive(Clone, PartialEq, Message)]
pub struct ProfilesData {
    #[prost(message, repeated, tag = "1")]
    pub resource_profiles: Vec<ResourceProfiles>,
}

#[derive(Clone, PartialEq, Message)]
pub struct ResourceProfiles {
    #[prost(message, optional, tag = "1")]
    pub resource: Option<Resource>,
    
    #[prost(message, repeated, tag = "2")]
    pub scope_profiles: Vec<ScopeProfiles>,
    
    #[prost(string, tag = "3")]
    pub schema_url: String,
}

#[derive(Clone, PartialEq, Message)]
pub struct ScopeProfiles {
    #[prost(message, optional, tag = "1")]
    pub scope: Option<InstrumentationScope>,
    
    #[prost(message, repeated, tag = "2")]
    pub profiles: Vec<ProfileContainer>,
    
    #[prost(string, tag = "3")]
    pub schema_url: String,
}

#[derive(Clone, PartialEq, Message)]
pub struct ProfileContainer {
    /// Profile唯一标识
    #[prost(bytes, tag = "1")]
    pub profile_id: Vec<u8>,
    
    /// 采样开始时间
    #[prost(fixed64, tag = "2")]
    pub start_time_unix_nano: u64,
    
    /// 采样结束时间
    #[prost(fixed64, tag = "3")]
    pub end_time_unix_nano: u64,
    
    /// 属性
    #[prost(message, repeated, tag = "4")]
    pub attributes: Vec<KeyValue>,
    
    /// 丢弃的属性数量
    #[prost(uint32, tag = "5")]
    pub dropped_attributes_count: u32,
    
    /// pprof格式的原始Profile数据
    #[prost(bytes, tag = "6")]
    pub profile: Vec<u8>,
}

// 辅助函数
impl ProfileContainer {
    /// 创建新的ProfileContainer
    pub fn new(
        profile_type: ProfileType,
        duration: Duration,
        pprof_data: Vec<u8>,
    ) -> Self {
        let profile_id = uuid::Uuid::new_v4().as_bytes().to_vec();
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;
        
        Self {
            profile_id,
            start_time_unix_nano: now - duration.as_nanos() as u64,
            end_time_unix_nano: now,
            attributes: vec![
                KeyValue {
                    key: "profile.type".to_string(),
                    value: Some(AnyValue {
                        value: Some(any_value::Value::StringValue(
                            profile_type.as_str().to_string()
                        )),
                    }),
                },
            ],
            dropped_attributes_count: 0,
            profile: pprof_data,
        }
    }
    
    /// 添加Trace关联
    pub fn link_to_trace(&mut self, trace_id: &[u8], span_id: &[u8]) {
        self.attributes.extend_from_slice(&[
            KeyValue {
                key: "trace_id".to_string(),
                value: Some(AnyValue {
                    value: Some(any_value::Value::BytesValue(
                        trace_id.to_vec()
                    )),
                }),
            },
            KeyValue {
                key: "span_id".to_string(),
                value: Some(AnyValue {
                    value: Some(any_value::Value::BytesValue(
                        span_id.to_vec()
                    )),
                }),
            },
        ]);
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ProfileType {
    Cpu,
    Heap,
    Goroutine,
    Mutex,
    Block,
    ThreadCreate,
}

impl ProfileType {
    pub fn as_str(&self) -> &'static str {
        match self {
            ProfileType::Cpu => "cpu",
            ProfileType::Heap => "heap",
            ProfileType::Goroutine => "goroutine",
            ProfileType::Mutex => "mutex",
            ProfileType::Block => "block",
            ProfileType::ThreadCreate => "threadcreate",
        }
    }
}
```

---

## 第三部分：采集方案

### 3.1 Go应用采集

#### 3.1.1 使用pprof

```go
package main

import (
    "bytes"
    "context"
    "runtime/pprof"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlpprofile"
    "go.opentelemetry.io/otel/exporters/otlp/otlpprofile/otlpprofilegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

func main() {
    // 创建Resource
    res, _ := resource.New(context.Background(),
        resource.WithAttributes(
            semconv.ServiceName("my-service"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("production"),
        ),
    )
    
    // 创建Profiles Exporter
    exporter, _ := otlpprofilegrpc.New(context.Background(),
        otlpprofilegrpc.WithEndpoint("localhost:4317"),
        otlpprofilegrpc.WithInsecure(),
    )
    
    // 创建Profiler
    profiler := otlpprofile.NewProfiler(
        otlpprofile.WithResource(res),
        otlpprofile.WithExporter(exporter),
        otlpprofile.WithProfilingInterval(60*time.Second),  // 60秒采样一次
    )
    
    // 启动持续性能剖析
    go profiler.Start(context.Background())
    
    // 应用主逻辑
    runApplication()
}

// 按需采集示例
func captureProfileOnDemand(ctx context.Context, profileType string) ([]byte, error) {
    var buf bytes.Buffer
    
    switch profileType {
    case "cpu":
        // CPU Profile (采样30秒)
        if err := pprof.StartCPUProfile(&buf); err != nil {
            return nil, err
        }
        time.Sleep(30 * time.Second)
        pprof.StopCPUProfile()
    
    case "heap":
        // Heap Profile
        if err := pprof.WriteHeapProfile(&buf); err != nil {
            return nil, err
        }
    
    case "goroutine":
        // Goroutine Profile
        profile := pprof.Lookup("goroutine")
        if err := profile.WriteTo(&buf, 0); err != nil {
            return nil, err
        }
    
    case "mutex":
        // Mutex Profile
        profile := pprof.Lookup("mutex")
        if err := profile.WriteTo(&buf, 0); err != nil {
            return nil, err
        }
    }
    
    return buf.Bytes(), nil
}

// 与Trace关联的Profile采集
func captureProfileWithTrace(ctx context.Context) {
    span := trace.SpanFromContext(ctx)
    spanCtx := span.SpanContext()
    
    // 采集CPU Profile
    var buf bytes.Buffer
    pprof.StartCPUProfile(&buf)
    
    // 业务逻辑
    doWork()
    
    pprof.StopCPUProfile()
    
    // 发送Profile,并关联TraceID和SpanID
    sendProfile(ProfileData{
        Type: "cpu",
        Data: buf.Bytes(),
        TraceID: spanCtx.TraceID().String(),
        SpanID: spanCtx.SpanID().String(),
    })
}
```

#### 3.1.2 持续性能剖析配置

```yaml
# Profiler配置
profiler:
  enabled: true
  
  # 采样配置
  sampling:
    # CPU采样率(Hz)
    cpu_sampling_rate: 100
    
    # Heap采样间隔(字节)
    heap_sampling_interval: 524288  # 512KB
    
    # 采样周期
    collection_interval: 60s
    
    # 采样时长
    cpu_profile_duration: 30s
  
  # Profile类型
  types:
    - cpu
    - heap
    - goroutine
    - mutex
    - block
  
  # 上传配置
  upload:
    endpoint: http://localhost:4317
    timeout: 30s
    batch_size: 10
    
  # 关联配置
  correlation:
    # 自动关联Trace
    enable_trace_correlation: true
    
    # 慢请求触发Profile
    slow_request_threshold: 5s
    slow_request_profile_duration: 10s
```

### 3.2 Java应用采集

```java
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.context.Context;
import io.opentelemetry.exporter.otlp.profiles.OtlpGrpcProfileExporter;
import io.opentelemetry.sdk.profiles.SdkProfilerProvider;

public class ProfileExample {
    public static void main(String[] args) {
        // 创建Profiles Exporter
        OtlpGrpcProfileExporter exporter = OtlpGrpcProfileExporter.builder()
            .setEndpoint("http://localhost:4317")
            .build();
        
        // 创建ProfilerProvider
        SdkProfilerProvider profilerProvider = SdkProfilerProvider.builder()
            .setResource(resource)
            .addProfileExporter(exporter)
            .build();
        
        // 启动持续性能剖析
        profilerProvider.start();
        
        // 应用逻辑
        runApplication();
    }
    
    // 使用async-profiler
    public static void captureJavaProfile() throws Exception {
        AsyncProfiler profiler = AsyncProfiler.getInstance();
        
        // 开始采样
        profiler.start("cpu,alloc", 60_000_000);  // 60秒
        
        // 业务逻辑
        doWork();
        
        // 停止并获取结果
        byte[] profileData = profiler.stop();
        
        // 发送到OTel Collector
        sendProfile(profileData);
    }
}
```

### 3.3 Python应用采集

```python
import cProfile
import pstats
import io
from opentelemetry import trace
from opentelemetry.exporter.otlp.proto.grpc.profiles import OTLPProfileExporter
from opentelemetry.sdk.profiles import ProfilerProvider
from opentelemetry.sdk.resources import Resource

def setup_profiling():
    # 创建Resource
    resource = Resource.create({
        "service.name": "my-python-service",
        "service.version": "1.0.0",
    })
    
    # 创建ProfilerProvider
    profiler_provider = ProfilerProvider(resource=resource)
    
    # 添加Exporter
    exporter = OTLPProfileExporter(endpoint="http://localhost:4317")
    profiler_provider.add_profile_exporter(exporter)
    
    return profiler_provider

def profile_function(func):
    """装饰器:为函数添加性能剖析"""
    def wrapper(*args, **kwargs):
        profiler = cProfile.Profile()
        profiler.enable()
        
        # 执行函数
        result = func(*args, **kwargs)
        
        profiler.disable()
        
        # 转换为pprof格式并发送
        s = io.StringIO()
        ps = pstats.Stats(profiler, stream=s)
        ps.print_stats()
        
        profile_data = convert_to_pprof(ps)
        send_profile(profile_data)
        
        return result
    return wrapper

@profile_function
def expensive_operation():
    # 业务逻辑
    pass

# 使用py-spy进行持续性能剖析
def start_continuous_profiling():
    import subprocess
    
    # 启动py-spy
    subprocess.Popen([
        "py-spy",
        "record",
        "--format", "speedscope",
        "--output", "/tmp/profile.json",
        "--pid", str(os.getpid()),
        "--duration", "60",
        "--rate", "100",
    ])
```

### 3.4 Rust应用采集

```rust
use pprof::ProfilerGuard;
use std::fs::File;
use std::time::Duration;

// 使用pprof-rs
pub fn capture_cpu_profile(duration: Duration) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let guard = ProfilerGuard::new(100)?;  // 100Hz采样率
    
    // 业务逻辑运行指定时长
    std::thread::sleep(duration);
    
    // 生成报告
    if let Ok(report) = guard.report().build() {
        let mut buf = Vec::new();
        report.pprof()?.write_to_vec(&mut buf)?;
        return Ok(buf);
    }
    
    Err("Failed to generate profile".into())
}

// 与Trace关联
pub async fn profile_with_trace<F, T>(
    tracer: &Tracer,
    name: &str,
    f: F,
) -> T
where
    F: FnOnce() -> T,
{
    let mut span = tracer.start(name);
    let span_ctx = span.span_context().clone();
    
    // 开始采样
    let guard = ProfilerGuard::new(100).unwrap();
    
    // 执行函数
    let result = f();
    
    // 停止采样并生成Profile
    if let Ok(report) = guard.report().build() {
        let mut buf = Vec::new();
        if report.pprof().unwrap().write_to_vec(&mut buf).is_ok() {
            // 发送Profile并关联Trace
            send_profile_with_trace(
                buf,
                span_ctx.trace_id(),
                span_ctx.span_id(),
            ).await;
        }
    }
    
    span.end();
    result
}

// 发送Profile到OTLP Collector
async fn send_profile_with_trace(
    pprof_data: Vec<u8>,
    trace_id: TraceId,
    span_id: SpanId,
) {
    let profile_container = ProfileContainer {
        profile_id: uuid::Uuid::new_v4().as_bytes().to_vec(),
        start_time_unix_nano: /* ... */,
        end_time_unix_nano: /* ... */,
        attributes: vec![
            KeyValue {
                key: "profile.type".to_string(),
                value: Some(AnyValue {
                    value: Some(any_value::Value::StringValue("cpu".to_string())),
                }),
            },
            KeyValue {
                key: "trace_id".to_string(),
                value: Some(AnyValue {
                    value: Some(any_value::Value::StringValue(
                        format!("{:032x}", trace_id.to_u128())
                    )),
                }),
            },
            KeyValue {
                key: "span_id".to_string(),
                value: Some(AnyValue {
                    value: Some(any_value::Value::StringValue(
                        format!("{:016x}", span_id.to_u64())
                    )),
                }),
            },
        ],
        dropped_attributes_count: 0,
        profile: pprof_data,
    };
    
    // 通过OTLP gRPC发送
    let mut client = ProfilesServiceClient::connect("http://localhost:4317")
        .await
        .unwrap();
    
    client.export(ExportProfilesServiceRequest {
        resource_profiles: vec![/* ... */],
    }).await.unwrap();
}
```

---

## 第四部分：传输与存储

### 4.1 Collector配置

```yaml
# otel-collector-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  # Profiles批处理
  batch/profiles:
    timeout: 10s
    send_batch_size: 100
    send_batch_max_size: 1000
  
  # 添加属性
  attributes/profiles:
    actions:
      - key: deployment.environment
        value: production
        action: upsert
      - key: cluster
        value: k8s-prod-01
        action: upsert
  
  # Profile与Trace关联
  span_profiles:
    # 自动关联
    enabled: true
    
    # 慢Span触发Profile采集
    slow_span_threshold: 5s
    
  # 采样
  probabilistic_sampler/profiles:
    sampling_percentage: 10  # 采样10%

exporters:
  # Pyroscope后端
  pyroscope:
    endpoint: http://pyroscope:4040
  
  # Grafana Phlare后端
  otlphttp/phlare:
    endpoint: http://phlare:4100/otlp
  
  # Datadog后端
  datadog/profiles:
    api:
      key: ${DD_API_KEY}
      site: datadoghq.com

service:
  pipelines:
    # Profiles管道
    profiles:
      receivers: [otlp]
      processors:
        - attributes/profiles
        - batch/profiles
        - probabilistic_sampler/profiles
      exporters: [pyroscope, otlphttp/phlare]
    
    # Traces管道 (用于关联)
    traces:
      receivers: [otlp]
      processors: [batch, span_profiles]
      exporters: [otlp]
```

### 4.2 存储后端选择

#### 4.2.1 Pyroscope

```yaml
# Pyroscope部署
apiVersion: apps/v1
kind: Deployment
metadata:
  name: pyroscope
spec:
  replicas: 1
  selector:
    matchLabels:
      app: pyroscope
  template:
    metadata:
      labels:
        app: pyroscope
    spec:
      containers:
        - name: pyroscope
          image: pyroscope/pyroscope:latest
          ports:
            - containerPort: 4040
          env:
            - name: PYROSCOPE_LOG_LEVEL
              value: debug
            - name: PYROSCOPE_STORAGE_PATH
              value: /var/lib/pyroscope
          volumeMounts:
            - name: data
              mountPath: /var/lib/pyroscope
      volumes:
        - name: data
          persistentVolumeClaim:
            claimName: pyroscope-pvc
```

#### 4.2.2 Grafana Phlare

```yaml
# Phlare配置
apiVersion: v1
kind: ConfigMap
metadata:
  name: phlare-config
data:
  config.yaml: |
    # Phlare配置
    target: all
    
    # OTLP接收
    otlp:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318
    
    # 存储
    storage:
      backend: s3
      s3:
        bucket_name: phlare-profiles
        endpoint: s3.amazonaws.com
        region: us-east-1
    
    # 查询
    querier:
      max_concurrent: 20
      query_timeout: 30s
```

---

## 第五部分：查询与分析

### 5.1 查询API

```bash
# Pyroscope查询API
# 1. 查询可用的Profile类型
curl 'http://pyroscope:4040/api/apps'

# 2. 查询特定时间范围的Profile
curl 'http://pyroscope:4040/render?from=now-1h&until=now&query=my-service.cpu&format=json'

# 3. 比较两个Profile
curl 'http://pyroscope:4040/render?from=now-2h&until=now-1h&query=my-service.cpu&format=json' \
     -X POST \
     -d '{"rightFrom":"now-1h","rightUntil":"now"}'

# 4. 根据标签查询
curl 'http://pyroscope:4040/render?from=now-1h&until=now&query=my-service.cpu{environment="production",region="us-east-1"}'
```

### 5.2 火焰图可视化

```html
<!-- 嵌入火焰图 -->
<!DOCTYPE html>
<html>
<head>
    <title>Flame Graph</title>
    <script src="https://cdn.jsdelivr.net/npm/d3@7"></script>
    <script src="https://cdn.jsdelivr.net/npm/d3-flame-graph@4"></script>
</head>
<body>
    <div id="chart"></div>
    <script>
        // 从Pyroscope获取数据
        fetch('http://pyroscope:4040/render?from=now-1h&until=now&query=my-service.cpu&format=json')
            .then(response => response.json())
            .then(data => {
                // 渲染火焰图
                const flamegraph = d3.flamegraph()
                    .width(960)
                    .height(540)
                    .cellHeight(18)
                    .transitionDuration(750)
                    .minFrameSize(5)
                    .transitionEase(d3.easeCubic)
                    .inverted(false)
                    .sort(true);
                
                d3.select("#chart")
                    .datum(data)
                    .call(flamegraph);
            });
    </script>
</body>
</html>
```

---

## 第六部分：与Traces关联

### 6.1 自动关联

```yaml
# Collector配置
processors:
  span_profiles:
    enabled: true
    
    # 所有Span自动触发Profile
    always_profile: false
    
    # 慢Span触发Profile
    slow_span_threshold: 5s
    slow_span_profile_duration: 10s
    
    # 错误Span触发Profile
    error_span_profile: true
    error_span_profile_duration: 10s
    
    # 采样率
    sampling_rate: 0.1  # 10%
```

### 6.2 手动关联

```go
// Go示例
func handleRequest(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    span := trace.SpanFromContext(ctx)
    spanCtx := span.SpanContext()
    
    // 判断是否需要Profile
    if shouldProfile(r) {
        // 开始CPU Profiling
        var buf bytes.Buffer
        pprof.StartCPUProfile(&buf)
        
        defer func() {
            pprof.StopCPUProfile()
            
            // 发送Profile并关联Trace
            sendProfileWithTrace(ProfileData{
                Type: "cpu",
                Data: buf.Bytes(),
                TraceID: spanCtx.TraceID().String(),
                SpanID: spanCtx.SpanID().String(),
                Timestamp: time.Now(),
            })
        }()
    }
    
    // 业务逻辑
    doWork()
}

func shouldProfile(r *http.Request) bool {
    // 1. 检查特殊header
    if r.Header.Get("X-Enable-Profiling") == "true" {
        return true
    }
    
    // 2. 基于概率采样
    if rand.Float64() < 0.01 {  // 1%
        return true
    }
    
    return false
}
```

### 6.3 查询关联的Profiles

```bash
# 根据TraceID查询关联的Profiles
curl 'http://phlare:4100/api/v1/query' \
  -d 'query=my-service.cpu{trace_id="5b8aa5a2d2c872e8321cf37308d69df2"}'

# 在Grafana中查询
# PromQL风格查询
sum(rate(my-service_cpu_total{trace_id="5b8aa5a2d2c872e8321cf37308d69df2"}[5m]))
```

---

## 第七部分：性能优化

### 7.1 采样策略

```yaml
# 多层采样
sampling:
  # Level 1: 基础采样(持续)
  continuous:
    enabled: true
    cpu_sample_rate: 100Hz
    heap_sample_interval: 524288  # 512KB
    interval: 60s
    percentage: 100%
  
  # Level 2: 条件触发
  conditional:
    # 慢请求
    slow_request:
      enabled: true
      threshold: 5s
      profile_duration: 10s
      sample_rate: 100%
    
    # 错误请求
    error_request:
      enabled: true
      profile_duration: 10s
      sample_rate: 50%
    
    # 高CPU
    high_cpu:
      enabled: true
      threshold: 80%
      profile_duration: 30s
      cooldown: 5m
  
  # Level 3: 按需(手动触发)
  on_demand:
    enabled: true
    max_duration: 300s
```

### 7.2 资源控制

```yaml
# 资源限制
resource_limits:
  # CPU开销
  cpu:
    max_overhead: 5%  # 最大5% CPU开销
    throttle_on_high_load: true
    high_load_threshold: 80%
  
  # 内存使用
  memory:
    max_profile_size: 10MB
    max_buffer_size: 100MB
    compression_enabled: true
  
  # 网络带宽
  network:
    max_upload_rate: 1MB/s
    batch_profiles: true
    batch_size: 10
  
  # 存储
  storage:
    max_profiles_per_hour: 60
    retention_period: 7d
    auto_cleanup: true
```

### 7.3 性能指标

```yaml
# 监控Profile性能
- profile_collection_duration_seconds
  # 采集耗时

- profile_size_bytes
  # Profile大小

- profile_upload_duration_seconds
  # 上传耗时

- profile_overhead_cpu_percent
  # CPU开销

- profile_overhead_memory_bytes
  # 内存开销

- profiles_collected_total
  # 采集总数

- profiles_dropped_total
  # 丢弃总数(资源限制)
```

---

## 第八部分：最佳实践

### 8.1 生产环境部署

```yaml
生产环境检查清单:
□ 采样率合理(持续<5% CPU开销)
□ 存储容量规划
□ 带宽评估
□ 隐私合规(脱敏函数名/文件名)
□ 访问控制(RBAC)
□ 自动化告警(采集失败、存储满)
□ 性能基线测试
□ 灰度发布
□ 回滚预案
□ 运维文档
```

### 8.2 故障排查流程

```text
1. 发现性能问题(高延迟/高CPU)
   │
   ▼
2. 查看Traces,定位慢Span
   │
   ▼
3. 根据TraceID/SpanID查询关联的Profile
   │
   ▼
4. 分析火焰图,识别热点函数
   │
   ▼
5. 对比历史Profile,确认回归
   │
   ▼
6. 代码优化
   │
   ▼
7. 压测验证,对比Profile
   │
   ▼
8. 发布修复
```

### 8.3 成本优化

```yaml
# 成本优化策略
cost_optimization:
  # 1. 智能采样
  sampling:
    # 正常流量低采样
    normal_traffic: 1%
    
    # 问题流量高采样
    slow_requests: 100%
    error_requests: 50%
    
  # 2. 数据压缩
  compression:
    enabled: true
    algorithm: gzip
    level: 6
  
  # 3. 存储分层
  storage_tiers:
    hot:
      duration: 7d
      storage_class: ssd
    
    warm:
      duration: 30d
      storage_class: hdd
    
    cold:
      duration: 90d
      storage_class: glacier
  
  # 4. 自动清理
  cleanup:
    enabled: true
    retention: 90d
    
    # 保留重要Profile
    keep_rules:
      - slow_requests
      - error_requests
      - manual_triggers
```

---

## 📚 参考资源

- [OTLP Profiles规范](https://github.com/open-telemetry/opentelemetry-proto/blob/main/opentelemetry/proto/profiles/v1/profiles.proto)
- [pprof格式](https://github.com/google/pprof/blob/main/proto/profile.proto)
- [Pyroscope文档](https://pyroscope.io/docs/)
- [Grafana Phlare文档](https://grafana.com/docs/phlare/)

---

**完整的Profiles集成指南!** 🎓
