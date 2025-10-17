# eBPF实践完整指南

> **版本**: 1.0  
> **日期**: 2025年10月17日  
> **状态**: ✅ 完整版

---

## 📋 目录

- [第一部分：eBPF概述](#第一部分ebpf概述)
- [第二部分：eBPF与可观测性](#第二部分ebpf与可观测性)
- [第三部分：eBPF Traces采集](#第三部分ebpf-traces采集)
- [第四部分：eBPF Metrics采集](#第四部分ebpf-metrics采集)
- [第五部分：eBPF Logs采集](#第五部分ebpf-logs采集)
- [第六部分：eBPF Profiles采集](#第六部分ebpf-profiles采集)
- [第七部分：生产环境部署](#第七部分生产环境部署)
- [第八部分：最佳实践](#第八部分最佳实践)

---

## 第一部分：eBPF概述

### 1.1 什么是eBPF?

**eBPF (extended Berkeley Packet Filter)** 是Linux内核的革命性技术,允许在内核中安全高效地运行沙箱程序,无需修改内核源码或加载内核模块。

#### 核心特性

```text
eBPF特性:
├── 安全性: 验证器确保程序安全
├── 高性能: 内核态执行,JIT编译
├── 可编程: C/Rust编写,灵活定制
├── 零侵入: 无需修改应用代码
├── 实时性: 内核事件即时捕获
└── 低开销: <5% CPU开销
```

#### eBPF在可观测性中的优势

| 维度 | 传统方式 | eBPF方式 |
|------|---------|---------|
| **代码侵入** | 需要SDK/Agent | 零代码修改 |
| **性能开销** | 5-15% | <5% |
| **数据粒度** | 应用层 | 内核+应用层 |
| **语言支持** | 特定语言SDK | 所有语言 |
| **部署复杂度** | 需重启应用 | 热加载 |
| **安全风险** | 应用内代码 | 内核验证器保护 |

### 1.2 eBPF架构

```text
┌─────────────────────────────────────────────────┐
│              User Space                         │
│  ┌───────────────────────────────────────────┐  │
│  │  OTel Collector                           │  │
│  │  ┌─────────────────────────────────────┐  │  │
│  │  │ eBPF Receiver                       │  │  │
│  │  │  - 读取eBPF Maps                    │  │  │
│  │  │  - 转换为OTLP格式                   │  │  │
│  │  └─────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────┘  │
└──────────────────┬──────────────────────────────┘
                   │ bpf() syscall
┌──────────────────▼──────────────────────────────┐
│              Kernel Space                        │
│  ┌───────────────────────────────────────────┐  │
│  │  eBPF Programs                            │  │
│  │  ┌─────────────┐  ┌──────────────┐       │  │
│  │  │ kprobes     │  │ tracepoints  │       │  │
│  │  └─────────────┘  └──────────────┘       │  │
│  │  ┌─────────────┐  ┌──────────────┐       │  │
│  │  │ uprobes     │  │ perf_events  │       │  │
│  │  └─────────────┘  └──────────────┘       │  │
│  └───────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────┐  │
│  │  eBPF Maps (数据共享)                      │  │
│  │  - Hash Map                               │  │
│  │  - Array Map                              │  │
│  │  - Perf Event Array                       │  │
│  │  - Ring Buffer                            │  │
│  └───────────────────────────────────────────┘  │
└─────────────────────────────────────────────────┘
         │            │            │
         ▼            ▼            ▼
    [Network]    [Syscalls]   [Functions]
```

### 1.3 eBPF程序类型

| 类型 | 说明 | 用途 |
|------|------|------|
| **kprobe** | 内核函数探针 | 监控内核函数调用 |
| **kretprobe** | 内核函数返回探针 | 捕获返回值和延迟 |
| **uprobe** | 用户空间函数探针 | 监控应用函数(如SSL) |
| **uretprobe** | 用户空间返回探针 | 捕获用户函数返回值 |
| **tracepoint** | 静态追踪点 | 稳定的内核事件 |
| **perf_event** | 性能事件 | CPU采样、硬件计数器 |
| **xdp** | eXpress Data Path | 高性能网络过滤 |
| **tc** | Traffic Control | 流量控制和镜像 |

---

## 第二部分：eBPF与可观测性

### 2.1 eBPF采集架构

```text
应用程序 (无需修改)
    │
    │ 系统调用、网络I/O、函数调用
    ▼
┌────────────────────────────────┐
│  Linux Kernel                  │
│  ┌──────────────────────────┐  │
│  │ eBPF Programs            │  │
│  │  - HTTP追踪              │  │
│  │  - TCP监控               │  │
│  │  - 函数延迟              │  │
│  │  - CPU采样               │  │
│  └────────┬─────────────────┘  │
│           │ 写入Maps           │
│  ┌────────▼─────────────────┐  │
│  │ eBPF Maps                │  │
│  └────────┬─────────────────┘  │
└───────────┼────────────────────┘
            │ 读取
┌───────────▼────────────────────┐
│ OTel Collector                 │
│  eBPF Receiver                 │
│   ├─ HTTP Traces               │
│   ├─ TCP Metrics               │
│   ├─ Latency Histograms        │
│   └─ CPU Profiles              │
└───────────┬────────────────────┘
            │ OTLP
┌───────────▼────────────────────┐
│ 后端 (Jaeger/Prometheus/...)   │
└────────────────────────────────┘
```

### 2.2 零代码可观测性

```yaml
# 无需修改应用代码,即可实现:
zero_instrumentation:
  traces:
    - HTTP请求追踪(L7)
    - gRPC调用追踪
    - Database查询追踪
    - Redis操作追踪
    - Kafka消息追踪
  
  metrics:
    - 请求速率、延迟、错误率
    - TCP连接数、重传率
    - 文件I/O吞吐量
    - 内存分配统计
  
  logs:
    - 系统调用日志
    - 安全事件(如execve)
    - 网络连接日志
  
  profiles:
    - CPU火焰图
    - Off-CPU分析
    - 内存分配追踪
```

---

## 第三部分：eBPF Traces采集

### 3.1 HTTP追踪

#### 3.1.1 eBPF程序(HTTP追踪)

```c
// http_trace.bpf.c
#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

// HTTP请求结构
struct http_request {
    __u64 timestamp_ns;
    __u32 pid;
    __u32 tid;
    char method[16];      // GET, POST, etc.
    char path[256];
    char host[256];
    __u32 status_code;
    __u64 duration_ns;
};

// Map: 存储进行中的请求
struct {
    __uint(type, BPF_MAP_TYPE_HASH);
    __uint(max_entries, 10240);
    __type(key, __u64);  // tid
    __type(value, struct http_request);
} active_requests SEC(".maps");

// Map: 完成的请求(发送到用户空间)
struct {
    __uint(type, BPF_MAP_TYPE_RINGBUF);
    __uint(max_entries, 256 * 1024);
} completed_requests SEC(".maps");

// Uprobe: SSL_write开始(捕获HTTP请求)
SEC("uprobe/SSL_write")
int BPF_KPROBE(ssl_write_entry, void *ssl, const void *buf, int num)
{
    __u64 tid = bpf_get_current_pid_tgid();
    __u64 ts = bpf_ktime_get_ns();
    
    struct http_request req = {};
    req.timestamp_ns = ts;
    req.pid = tid >> 32;
    req.tid = tid;
    
    // 解析HTTP请求头
    char line[512];
    bpf_probe_read_user(&line, sizeof(line), buf);
    
    // 提取方法(GET/POST/...)
    if (line[0] == 'G' && line[1] == 'E' && line[2] == 'T') {
        __builtin_memcpy(req.method, "GET", 4);
    } else if (line[0] == 'P' && line[1] == 'O' && line[2] == 'S' && line[3] == 'T') {
        __builtin_memcpy(req.method, "POST", 5);
    }
    
    // 提取路径
    // 简化示例,实际需要完整的HTTP解析
    char *path_start = line + 4;  // 跳过"GET "
    int i = 0;
    for (; i < 255 && path_start[i] != ' '; i++) {
        req.path[i] = path_start[i];
    }
    
    // 保存请求开始状态
    bpf_map_update_elem(&active_requests, &tid, &req, BPF_ANY);
    
    return 0;
}

// Uretprobe: SSL_write返回(计算延迟)
SEC("uretprobe/SSL_write")
int BPF_KRETPROBE(ssl_write_exit, int ret)
{
    __u64 tid = bpf_get_current_pid_tgid();
    
    struct http_request *req = bpf_map_lookup_elem(&active_requests, &tid);
    if (!req) {
        return 0;
    }
    
    // 计算延迟
    __u64 now = bpf_ktime_get_ns();
    req->duration_ns = now - req->timestamp_ns;
    
    // 发送完成的请求到用户空间
    bpf_ringbuf_output(&completed_requests, req, sizeof(*req), 0);
    
    // 清理
    bpf_map_delete_elem(&active_requests, &tid);
    
    return 0;
}

char LICENSE[] SEC("license") = "GPL";
```

#### 3.1.2 用户空间处理(Rust)

```rust
use aya::{Bpf, programs::{UProbe, KProbe}, maps::RingBuf};
use aya::util::online_cpus;
use bytes::BytesMut;

#[repr(C)]
#[derive(Debug, Clone)]
struct HttpRequest {
    timestamp_ns: u64,
    pid: u32,
    tid: u32,
    method: [u8; 16],
    path: [u8; 256],
    host: [u8; 256],
    status_code: u32,
    duration_ns: u64,
}

pub struct EbpfHttpTracer {
    bpf: Bpf,
}

impl EbpfHttpTracer {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        // 加载eBPF程序
        let mut bpf = Bpf::load_file("http_trace.bpf.o")?;
        
        // Attach uprobe到SSL_write
        let program: &mut UProbe = bpf.program_mut("ssl_write_entry").unwrap().try_into()?;
        program.load()?;
        program.attach(Some("SSL_write"), 0, "/usr/lib/libssl.so.3", None)?;
        
        // Attach uretprobe
        let program: &mut UProbe = bpf.program_mut("ssl_write_exit").unwrap().try_into()?;
        program.load()?;
        program.attach(Some("SSL_write"), 0, "/usr/lib/libssl.so.3", None)?;
        
        Ok(Self { bpf })
    }
    
    pub async fn collect_traces(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // 读取Ring Buffer
        let mut ring_buf = RingBuf::try_from(
            self.bpf.map_mut("completed_requests").unwrap()
        )?;
        
        loop {
            // 轮询事件
            if let Some(data) = ring_buf.next() {
                let req: HttpRequest = unsafe {
                    std::ptr::read(data.as_ptr() as *const HttpRequest)
                };
                
                // 转换为OTLP Span
                let span = self.http_request_to_span(req);
                
                // 发送到Collector
                self.send_span(span).await?;
            }
        }
    }
    
    fn http_request_to_span(&self, req: HttpRequest) -> Span {
        let method = String::from_utf8_lossy(&req.method)
            .trim_end_matches('\0')
            .to_string();
        let path = String::from_utf8_lossy(&req.path)
            .trim_end_matches('\0')
            .to_string();
        
        Span {
            trace_id: generate_trace_id(),
            span_id: generate_span_id(),
            name: format!("{} {}", method, path),
            kind: SpanKind::Server,
            start_time_unix_nano: req.timestamp_ns,
            end_time_unix_nano: req.timestamp_ns + req.duration_ns,
            attributes: vec![
                KeyValue {
                    key: "http.method".to_string(),
                    value: Some(AnyValue {
                        value: Some(any_value::Value::StringValue(method)),
                    }),
                },
                KeyValue {
                    key: "http.target".to_string(),
                    value: Some(AnyValue {
                        value: Some(any_value::Value::StringValue(path)),
                    }),
                },
                KeyValue {
                    key: "http.status_code".to_string(),
                    value: Some(AnyValue {
                        value: Some(any_value::Value::IntValue(req.status_code as i64)),
                    }),
                },
                KeyValue {
                    key: "process.pid".to_string(),
                    value: Some(AnyValue {
                        value: Some(any_value::Value::IntValue(req.pid as i64)),
                    }),
                },
            ],
            ..Default::default()
        }
    }
}
```

### 3.2 gRPC追踪

```c
// grpc_trace.bpf.c
// 类似HTTP追踪,但针对gRPC的特定格式

SEC("uprobe/grpc_call_start")
int BPF_KPROBE(grpc_call_start, void *call, const char *method)
{
    // 捕获gRPC调用开始
    // 提取method名称
    // 记录开始时间
}

SEC("uretprobe/grpc_call_end")
int BPF_KRETPROBE(grpc_call_end, int status)
{
    // 捕获gRPC调用结束
    // 计算延迟
    // 提取状态码
    // 生成Span
}
```

### 3.3 Database追踪

```c
// mysql_trace.bpf.c
SEC("uprobe/mysql_real_query")
int BPF_KPROBE(mysql_query, void *mysql, const char *query, unsigned long length)
{
    // 捕获MySQL查询
    __u64 tid = bpf_get_current_pid_tgid();
    __u64 ts = bpf_ktime_get_ns();
    
    struct db_query q = {};
    q.timestamp_ns = ts;
    q.pid = tid >> 32;
    
    // 复制SQL语句(限制长度)
    bpf_probe_read_user_str(q.statement, sizeof(q.statement), query);
    
    bpf_map_update_elem(&active_queries, &tid, &q, BPF_ANY);
    return 0;
}

SEC("uretprobe/mysql_real_query")
int BPF_KRETPROBE(mysql_query_exit, int ret)
{
    // 查询完成,生成Span
    // 包含SQL语句、执行时间、结果
}
```

---

## 第四部分：eBPF Metrics采集

### 4.1 TCP连接指标

```c
// tcp_metrics.bpf.c
struct tcp_metrics {
    __u64 connections_total;
    __u64 packets_sent;
    __u64 packets_received;
    __u64 retransmits;
    __u64 bytes_sent;
    __u64 bytes_received;
};

struct {
    __uint(type, BPF_MAP_TYPE_HASH);
    __type(key, __u32);  // dport
    __type(value, struct tcp_metrics);
    __uint(max_entries, 1024);
} tcp_stats SEC(".maps");

// Tracepoint: TCP连接建立
SEC("tracepoint/sock/inet_sock_set_state")
int trace_tcp_state(struct trace_event_raw_inet_sock_set_state *ctx)
{
    if (ctx->newstate == TCP_ESTABLISHED) {
        __u32 dport = ctx->dport;
        
        struct tcp_metrics *m = bpf_map_lookup_elem(&tcp_stats, &dport);
        if (m) {
            __sync_fetch_and_add(&m->connections_total, 1);
        } else {
            struct tcp_metrics new_m = { .connections_total = 1 };
            bpf_map_update_elem(&tcp_stats, &dport, &new_m, BPF_ANY);
        }
    }
    return 0;
}

// Kprobe: TCP重传
SEC("kprobe/tcp_retransmit_skb")
int BPF_KPROBE(tcp_retransmit, struct sock *sk)
{
    __u16 dport = sk->__sk_common.skc_dport;
    dport = bpf_ntohs(dport);
    __u32 port = dport;
    
    struct tcp_metrics *m = bpf_map_lookup_elem(&tcp_stats, &port);
    if (m) {
        __sync_fetch_and_add(&m->retransmits, 1);
    }
    return 0;
}
```

```rust
// 用户空间读取指标
pub async fn collect_tcp_metrics(&mut self) -> Result<Vec<Metric>, Box<dyn std::error::Error>> {
    let tcp_stats: HashMap<_, _, _> = HashMap::try_from(
        self.bpf.map("tcp_stats").unwrap()
    )?;
    
    let mut metrics = Vec::new();
    
    for (port, stats) in tcp_stats.iter() {
        metrics.push(Metric {
            name: "tcp.connections.total".to_string(),
            unit: "connections".to_string(),
            data: Some(metric::Data::Sum(Sum {
                data_points: vec![
                    NumberDataPoint {
                        attributes: vec![
                            KeyValue {
                                key: "port".to_string(),
                                value: Some(AnyValue {
                                    value: Some(any_value::Value::IntValue(*port as i64)),
                                }),
                            },
                        ],
                        value: Some(number_data_point::Value::AsInt(stats.connections_total as i64)),
                        ..Default::default()
                    },
                ],
                aggregation_temporality: AggregationTemporality::Cumulative as i32,
                is_monotonic: true,
            })),
        });
        
        metrics.push(Metric {
            name: "tcp.retransmits.total".to_string(),
            unit: "packets".to_string(),
            data: Some(metric::Data::Sum(Sum {
                data_points: vec![
                    NumberDataPoint {
                        attributes: vec![
                            KeyValue {
                                key: "port".to_string(),
                                value: Some(AnyValue {
                                    value: Some(any_value::Value::IntValue(*port as i64)),
                                }),
                            },
                        ],
                        value: Some(number_data_point::Value::AsInt(stats.retransmits as i64)),
                        ..Default::default()
                    },
                ],
                aggregation_temporality: AggregationTemporality::Cumulative as i32,
                is_monotonic: true,
            })),
        });
    }
    
    Ok(metrics)
}
```

### 4.2 文件I/O指标

```c
// io_metrics.bpf.c
struct io_stats {
    __u64 read_count;
    __u64 write_count;
    __u64 read_bytes;
    __u64 write_bytes;
    __u64 read_latency_us;
    __u64 write_latency_us;
};

// Tracepoint: read系统调用
SEC("tracepoint/syscalls/sys_enter_read")
int trace_read_entry(struct trace_event_raw_sys_enter *ctx)
{
    __u64 tid = bpf_get_current_pid_tgid();
    __u64 ts = bpf_ktime_get_ns();
    
    bpf_map_update_elem(&io_start, &tid, &ts, BPF_ANY);
    return 0;
}

SEC("tracepoint/syscalls/sys_exit_read")
int trace_read_exit(struct trace_event_raw_sys_exit *ctx)
{
    __u64 tid = bpf_get_current_pid_tgid();
    __u64 *start_ts = bpf_map_lookup_elem(&io_start, &tid);
    
    if (start_ts) {
        __u64 latency = bpf_ktime_get_ns() - *start_ts;
        __u32 pid = tid >> 32;
        
        struct io_stats *stats = bpf_map_lookup_elem(&io_metrics, &pid);
        if (stats) {
            __sync_fetch_and_add(&stats->read_count, 1);
            __sync_fetch_and_add(&stats->read_bytes, ctx->ret);
            __sync_fetch_and_add(&stats->read_latency_us, latency / 1000);
        }
        
        bpf_map_delete_elem(&io_start, &tid);
    }
    return 0;
}
```

---

## 第五部分：eBPF Logs采集

### 5.1 系统调用日志

```c
// syscall_logs.bpf.c
struct syscall_event {
    __u64 timestamp_ns;
    __u32 pid;
    char comm[16];
    __u32 syscall_nr;
    __u64 args[6];
    __s64 ret;
};

SEC("tracepoint/raw_syscalls/sys_enter")
int trace_sys_enter(struct trace_event_raw_sys_enter *ctx)
{
    __u32 pid = bpf_get_current_pid_tgid() >> 32;
    
    // 只记录特定进程或特定系统调用
    if (pid != target_pid && target_pid != 0) {
        return 0;
    }
    
    struct syscall_event event = {};
    event.timestamp_ns = bpf_ktime_get_ns();
    event.pid = pid;
    event.syscall_nr = ctx->id;
    bpf_get_current_comm(&event.comm, sizeof(event.comm));
    
    // 复制参数
    for (int i = 0; i < 6; i++) {
        event.args[i] = ctx->args[i];
    }
    
    bpf_ringbuf_output(&events, &event, sizeof(event), 0);
    return 0;
}
```

### 5.2 安全审计日志

```c
// security_audit.bpf.c
// 监控敏感操作

// 1. 监控进程执行
SEC("tracepoint/syscalls/sys_enter_execve")
int trace_execve(struct trace_event_raw_sys_enter *ctx)
{
    char filename[256];
    bpf_probe_read_user_str(filename, sizeof(filename), (void *)ctx->args[0]);
    
    struct audit_log log = {
        .type = AUDIT_EXEC,
        .timestamp_ns = bpf_ktime_get_ns(),
        .pid = bpf_get_current_pid_tgid() >> 32,
    };
    __builtin_memcpy(log.data, filename, sizeof(filename));
    
    bpf_ringbuf_output(&audit_events, &log, sizeof(log), 0);
    return 0;
}

// 2. 监控文件删除
SEC("tracepoint/syscalls/sys_enter_unlink")
int trace_unlink(struct trace_event_raw_sys_enter *ctx)
{
    // 记录文件删除操作
}

// 3. 监控权限提升
SEC("tracepoint/syscalls/sys_enter_setuid")
int trace_setuid(struct trace_event_raw_sys_enter *ctx)
{
    // 记录权限变更
}
```

---

## 第六部分：eBPF Profiles采集

### 6.1 CPU性能剖析

```c
// cpu_profile.bpf.c
struct {
    __uint(type, BPF_MAP_TYPE_STACK_TRACE);
    __uint(max_entries, 10000);
    __uint(key_size, sizeof(__u32));
    __uint(value_size, 127 * sizeof(__u64));  // 最多127层调用栈
} stack_traces SEC(".maps");

struct {
    __uint(type, BPF_MAP_TYPE_HASH);
    __type(key, __u32);  // stack_id
    __type(value, __u64);  // count
    __uint(max_entries, 10000);
} stack_counts SEC(".maps");

// Perf Event: 定时CPU采样
SEC("perf_event")
int do_perf_event(struct bpf_perf_event_data *ctx)
{
    __u32 pid = bpf_get_current_pid_tgid() >> 32;
    
    // 只采样特定进程
    if (target_pid != 0 && pid != target_pid) {
        return 0;
    }
    
    // 获取调用栈
    __u32 stack_id = bpf_get_stackid(ctx, &stack_traces, BPF_F_USER_STACK);
    if (stack_id >= 0) {
        // 增加调用栈计数
        __u64 *count = bpf_map_lookup_elem(&stack_counts, &stack_id);
        if (count) {
            __sync_fetch_and_add(count, 1);
        } else {
            __u64 new_count = 1;
            bpf_map_update_elem(&stack_counts, &stack_id, &new_count, BPF_ANY);
        }
    }
    
    return 0;
}
```

```rust
// 用户空间生成pprof格式
pub fn generate_pprof_profile(&self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let stack_traces: StackTraceMap = StackTraceMap::try_from(
        self.bpf.map("stack_traces").unwrap()
    )?;
    
    let stack_counts: HashMap<u32, u64> = HashMap::try_from(
        self.bpf.map("stack_counts").unwrap()
    )?;
    
    let mut profile = pprof::Profile::default();
    
    // 构建pprof Profile
    for (stack_id, count) in stack_counts.iter() {
        if let Ok(stack) = stack_traces.get(stack_id, 0) {
            let mut locations = Vec::new();
            
            // 解析调用栈地址
            for addr in stack.frames() {
                // 地址 -> 函数名 (需要符号表)
                let function_name = resolve_symbol(addr)?;
                
                locations.push(pprof::Location {
                    id: addr as u64,
                    address: addr as u64,
                    line: vec![pprof::Line {
                        function_id: function_name.as_ptr() as u64,
                        line: 0,
                    }],
                    ..Default::default()
                });
            }
            
            profile.sample.push(pprof::Sample {
                location_id: locations.iter().map(|l| l.id).collect(),
                value: vec![*count as i64],
                ..Default::default()
            });
        }
    }
    
    // 序列化为protobuf
    let mut buf = Vec::new();
    profile.write_to_vec(&mut buf)?;
    
    Ok(buf)
}
```

### 6.2 Off-CPU分析

```c
// offcpu_profile.bpf.c
// 监控线程阻塞时间

SEC("tracepoint/sched/sched_switch")
int trace_sched_switch(struct trace_event_raw_sched_switch *ctx)
{
    __u64 ts = bpf_ktime_get_ns();
    __u32 prev_pid = ctx->prev_pid;
    __u32 next_pid = ctx->next_pid;
    
    // prev线程被切换出去(开始阻塞)
    if (prev_pid != 0) {
        bpf_map_update_elem(&block_start, &prev_pid, &ts, BPF_ANY);
    }
    
    // next线程被切换进来(结束阻塞)
    if (next_pid != 0) {
        __u64 *start_ts = bpf_map_lookup_elem(&block_start, &next_pid);
        if (start_ts) {
            __u64 block_time = ts - *start_ts;
            
            // 记录阻塞时间和调用栈
            __u32 stack_id = bpf_get_stackid(ctx, &stack_traces, BPF_F_USER_STACK);
            
            struct block_event event = {
                .pid = next_pid,
                .duration_ns = block_time,
                .stack_id = stack_id,
            };
            
            bpf_ringbuf_output(&block_events, &event, sizeof(event), 0);
            
            bpf_map_delete_elem(&block_start, &next_pid);
        }
    }
    
    return 0;
}
```

---

## 第七部分：生产环境部署

### 7.1 OTel Collector集成

```yaml
# otel-collector-config.yaml
receivers:
  # eBPF Receiver
  ebpf:
    # 配置
    endpoint: 0.0.0.0:4317
    
    # Traces
    traces:
      protocols:
        - http
        - grpc
        - mysql
        - redis
      
      # 过滤
      filters:
        - min_duration: 100ms
        - http_status: ">=400"
    
    # Metrics
    metrics:
      tcp_connections: true
      tcp_retransmits: true
      file_io: true
      syscalls: false  # 高开销,按需启用
    
    # Logs
    logs:
      security_audit: true
      syscalls: false
      
      # 审计规则
      audit_rules:
        - execve
        - unlink
        - setuid
    
    # Profiles
    profiles:
      cpu_sampling_rate: 100  # Hz
      collect_interval: 60s
      target_pids: []  # 空=所有进程
    
    # 资源限制
    resource_limits:
      max_memory_mb: 500
      max_cpu_percent: 5

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
  
  # 添加环境标签
  resource:
    attributes:
      - key: ebpf.enabled
        value: true
        action: upsert
      - key: collection.method
        value: ebpf
        action: upsert

exporters:
  otlp:
    endpoint: backend:4317

service:
  pipelines:
    traces:
      receivers: [ebpf]
      processors: [batch, resource]
      exporters: [otlp]
    
    metrics:
      receivers: [ebpf]
      processors: [batch, resource]
      exporters: [otlp]
    
    logs:
      receivers: [ebpf]
      processors: [batch, resource]
      exporters: [otlp]
    
    profiles:
      receivers: [ebpf]
      processors: [batch, resource]
      exporters: [otlp]
```

### 7.2 Kubernetes部署

```yaml
# ebpf-collector-daemonset.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: ebpf-collector
  namespace: observability
spec:
  selector:
    matchLabels:
      app: ebpf-collector
  template:
    metadata:
      labels:
        app: ebpf-collector
    spec:
      hostNetwork: true
      hostPID: true
      
      # 需要特权模式加载eBPF程序
      containers:
        - name: collector
          image: otel/opentelemetry-collector-contrib:0.89.0-ebpf
          
          securityContext:
            privileged: true
            capabilities:
              add:
                - SYS_ADMIN
                - SYS_RESOURCE
                - NET_ADMIN
          
          volumeMounts:
            - name: config
              mountPath: /etc/otelcol
            - name: sys
              mountPath: /sys
              readOnly: true
            - name: debugfs
              mountPath: /sys/kernel/debug
            - name: bpffs
              mountPath: /sys/fs/bpf
          
          resources:
            requests:
              cpu: 200m
              memory: 256Mi
            limits:
              cpu: 1000m
              memory: 512Mi
      
      volumes:
        - name: config
          configMap:
            name: ebpf-collector-config
        - name: sys
          hostPath:
            path: /sys
        - name: debugfs
          hostPath:
            path: /sys/kernel/debug
        - name: bpffs
          hostPath:
            path: /sys/fs/bpf
```

### 7.3 内核要求

```yaml
# 最低内核版本要求
kernel_requirements:
  minimum_version: "4.19"  # 基础eBPF支持
  recommended_version: "5.10"  # BTF、CO-RE支持
  
  # 必需的内核配置
  required_configs:
    - CONFIG_BPF=y
    - CONFIG_BPF_SYSCALL=y
    - CONFIG_BPF_JIT=y
    - CONFIG_HAVE_EBPF_JIT=y
    - CONFIG_BPF_EVENTS=y
    - CONFIG_KPROBES=y
    - CONFIG_UPROBES=y
    - CONFIG_TRACEPOINTS=y
  
  # 推荐的内核配置
  recommended_configs:
    - CONFIG_DEBUG_INFO_BTF=y  # BTF类型信息
    - CONFIG_DEBUG_INFO_BTF_MODULES=y

# 检查命令
check_commands:
  - "uname -r"  # 检查内核版本
  - "zgrep CONFIG_BPF /proc/config.gz"  # 检查配置
  - "ls /sys/kernel/debug/tracing"  # 检查debugfs
```

---

## 第八部分：最佳实践

### 8.1 性能优化

```yaml
# 性能优化建议
performance_tuning:
  # 1. Map大小优化
  map_sizing:
    hash_maps: 10240  # 根据预期并发调整
    ring_buffers: 256KB  # 事件缓冲区大小
    stack_traces: 10000  # 调用栈缓存
  
  # 2. 采样策略
  sampling:
    cpu_profile_rate: 100Hz  # 不要超过100Hz
    trace_sampling: 1%  # 高流量场景降低采样
    metric_aggregation: 10s  # 本地聚合减少开销
  
  # 3. 过滤规则
  filtering:
    # 在eBPF程序中过滤,减少用户空间开销
    - exclude_internal_traffic: true
    - min_duration: 100ms
    - http_methods: [GET, POST, PUT, DELETE]
  
  # 4. 资源限制
  resource_limits:
    max_cpu_percent: 5
    max_memory_mb: 500
    max_events_per_sec: 10000

# 性能指标监控
metrics:
  - ebpf_program_run_time_ns
  - ebpf_map_operations_total
  - ebpf_events_processed_total
  - ebpf_events_dropped_total
  - ebpf_cpu_overhead_percent
```

### 8.2 安全加固

```yaml
# 安全最佳实践
security:
  # 1. 最小权限
  least_privilege:
    # 使用CAP_BPF而非CAP_SYS_ADMIN(kernel>=5.8)
    capabilities:
      - CAP_BPF
      - CAP_PERFMON
      - CAP_NET_ADMIN
  
  # 2. 验证器限制
  verifier:
    max_instructions: 1000000
    stack_size: 512
    complexity_limit: 1000000
  
  # 3. 数据脱敏
  data_sanitization:
    - remove_sensitive_args: true
    - hash_user_data: true
    - truncate_large_payloads: true
  
  # 4. 审计日志
  audit:
    log_ebpf_loads: true
    log_program_attach: true
    log_map_access: true

# 安全检查清单
security_checklist:
  □ eBPF程序通过验证器检查
  □ 使用最小必要权限
  □ 敏感数据已脱敏
  □ 定期安全审计
  □ 监控异常行为
  □ 更新到最新内核(安全补丁)
```

### 8.3 故障排查

```bash
# 常见问题排查

# 1. eBPF程序加载失败
# 检查内核配置
zgrep CONFIG_BPF /proc/config.gz

# 查看验证器日志
bpftool prog load http_trace.bpf.o /sys/fs/bpf/http_trace

# 2. 权限不足
# 检查capabilities
capsh --print | grep bpf

# 临时授予权限(开发环境)
sudo setcap cap_sys_admin,cap_bpf=ep ./otel-collector

# 3. 没有数据采集
# 检查Map内容
bpftool map dump name tcp_stats

# 检查Ring Buffer
bpftool map dump name events

# 查看加载的程序
bpftool prog list

# 查看附加点
bpftool perf list

# 4. 性能问题
# 查看eBPF统计
bpftool prog show --json | jq

# 内核日志
dmesg | grep -i bpf

# perf分析eBPF开销
perf record -e bpf:* -a sleep 10
perf report
```

### 8.4 生产部署检查清单

```yaml
production_checklist:
  前期准备:
    □ 内核版本≥4.19(推荐≥5.10)
    □ 内核配置完整
    □ BTF支持(CO-RE)
    □ 符号表准备(用户空间调用栈解析)
    □ 性能基线测试
  
  部署配置:
    □ 采样率合理(<5% CPU开销)
    □ Map大小合理
    □ 过滤规则生效
    □ 资源限制配置
    □ 数据脱敏规则
  
  监控告警:
    □ eBPF程序健康监控
    □ 性能开销告警
    □ 事件丢失告警
    □ 内存使用告警
  
  灰度发布:
    □ 少量节点试点
    □ 性能对比测试
    □ 逐步扩大范围
    □ 回滚预案
  
  运维文档:
    □ 部署文档
    □ 故障排查手册
    □ 性能调优指南
    □ 应急响应流程
```

---

## 📚 参考资源

### 官方文档

- [eBPF官方文档](https://ebpf.io/what-is-ebpf/)
- [BCC工具集](https://github.com/iovisor/bcc)
- [libbpf](https://github.com/libbpf/libbpf)
- [aya (Rust eBPF)](https://aya-rs.dev/)

### 书籍

- "BPF Performance Tools" by Brendan Gregg
- "Linux Observability with BPF" by David Calavera & Lorenzo Fontana

### 工具

- `bpftool`: eBPF程序和Map管理
- `bpftrace`: 动态追踪语言
- `kubectl-trace`: Kubernetes eBPF追踪

---

**完整的eBPF实践指南!** 🎓
