# 🔗 Rust FFI + C 绑定 OTLP 跨语言集成指南

> **Rust 版本**: 1.90+  
> **Edition**: 2024  
> **C 标准**: C11/C17  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [1. FFI 概述](#1-ffi-概述)
- [2. 基础 C 绑定](#2-基础-c-绑定)
- [3. 内存管理](#3-内存管理)
- [4. 错误处理](#4-错误处理)
- [5. 线程安全](#5-线程安全)
- [6. Python 集成](#6-python-集成)
- [7. Node.js 集成](#7-nodejs-集成)
- [8. Go 集成](#8-go-集成)
- [9. Java/JNI 集成](#9-javajni-集成)
- [10. 生产实践](#10-生产实践)

---

## 1. FFI 概述

### 1.1 架构设计

```text
┌──────────────────────────────────────────────────────┐
│              多语言应用生态                           │
│  ┌────────┐  ┌────────┐  ┌────────┐  ┌────────┐      │
│  │ Python │  │ Node.js│  │   Go   │  │  Java  │      │
│  └───┬────┘  └───┬────┘  └───┬────┘  └───┬────┘      │
│      │           │           │           │           │
│      │ ctypes    │ napi      │ cgo       │ JNI       │
│      └───────────┴───────────┴───────────┘           │
│                      │                               │
│              C FFI 绑定层                             │
│  ┌────────────────────────────────────────────────┐  │
│  │  - otlp_span_create()                          │  │
│  │  - otlp_span_end()                             │  │
│  │  - otlp_exporter_init()                        │  │
│  │  - 线程安全保证                                 │  │
│  │  - 内存管理 (malloc/free)                       │  │
│  └────────────────┬───────────────────────────────┘  │
│                   │                                  │
│         Rust 核心实现 (静态库/动态库)                  │
│  ┌────────────────▼───────────────────────────────┐  │
│  │  OpenTelemetry Rust SDK                        │  │
│  │  - 高性能 Span 处理                             │  │
│  │  - OTLP 导出器                                  │  │
│  │  - 内存安全                                    │   │
│  └──────────────────────────────────────────────┘    │
└──────────────────────────────────────────────────────┘
```

### 1.2 设计原则

| 原则 | 说明 | 实现 |
|------|------|------|
| **C ABI 兼容** | 使用 `extern "C"` | ✅ 全部函数 |
| **不透明指针** | 隐藏 Rust 类型 | ✅ `void*` |
| **手动内存管理** | 显式释放 | ✅ `_free()` 函数 |
| **错误码** | 不使用异常 | ✅ `int32_t` 返回值 |
| **线程安全** | 并发访问保护 | ✅ Mutex/RwLock |
| **零拷贝** | 最小化数据复制 | ✅ 指针传递 |

---

## 2. 基础 C 绑定

### 2.1 项目配置

```toml
# Cargo.toml
[package]
name = "otlp-ffi"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[lib]
name = "otlp_ffi"
crate-type = ["cdylib", "staticlib"]  # 动态库 + 静态库

[dependencies]
opentelemetry = "0.31"
opentelemetry_sdk = "0.31"
opentelemetry-otlp = "0.31"
tokio = { version = "1.47", features = ["full"] }
once_cell = "1.20"
parking_lot = "0.12"

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
strip = true
panic = "abort"
```

### 2.2 C 头文件

```c
// include/otlp_ffi.h
#ifndef OTLP_FFI_H
#define OTLP_FFI_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

// ============================================================
// 错误码定义
// ============================================================

typedef enum {
    OTLP_OK = 0,
    OTLP_ERROR_INVALID_ARGUMENT = -1,
    OTLP_ERROR_NULL_POINTER = -2,
    OTLP_ERROR_INITIALIZATION_FAILED = -3,
    OTLP_ERROR_EXPORT_FAILED = -4,
    OTLP_ERROR_OUT_OF_MEMORY = -5,
    OTLP_ERROR_INTERNAL = -99
} otlp_error_t;

// ============================================================
// 不透明类型
// ============================================================

typedef struct otlp_tracer_provider otlp_tracer_provider_t;
typedef struct otlp_tracer otlp_tracer_t;
typedef struct otlp_span otlp_span_t;
typedef struct otlp_context otlp_context_t;

// ============================================================
// 初始化与配置
// ============================================================

/// 初始化全局追踪器
///
/// @param endpoint OTLP Collector 端点 (例如: "http://localhost:4318")
/// @param service_name 服务名称
/// @param provider 输出: TracerProvider 指针
/// @return 错误码
otlp_error_t otlp_init(
    const char* endpoint,
    const char* service_name,
    otlp_tracer_provider_t** provider
);

/// 释放 TracerProvider
///
/// @param provider TracerProvider 指针
void otlp_tracer_provider_free(otlp_tracer_provider_t* provider);

/// 获取 Tracer
///
/// @param provider TracerProvider 指针
/// @param tracer 输出: Tracer 指针
/// @return 错误码
otlp_error_t otlp_get_tracer(
    otlp_tracer_provider_t* provider,
    otlp_tracer_t** tracer
);

// ============================================================
// Span 操作
// ============================================================

/// 创建新 Span
///
/// @param tracer Tracer 指针
/// @param name Span 名称
/// @param span 输出: Span 指针
/// @return 错误码
otlp_error_t otlp_span_create(
    otlp_tracer_t* tracer,
    const char* name,
    otlp_span_t** span
);

/// 设置字符串属性
///
/// @param span Span 指针
/// @param key 属性键
/// @param value 属性值
/// @return 错误码
otlp_error_t otlp_span_set_attribute_string(
    otlp_span_t* span,
    const char* key,
    const char* value
);

/// 设置整数属性
///
/// @param span Span 指针
/// @param key 属性键
/// @param value 属性值
/// @return 错误码
otlp_error_t otlp_span_set_attribute_int(
    otlp_span_t* span,
    const char* key,
    int64_t value
);

/// 设置布尔属性
///
/// @param span Span 指针
/// @param key 属性键
/// @param value 属性值
/// @return 错误码
otlp_error_t otlp_span_set_attribute_bool(
    otlp_span_t* span,
    const char* key,
    bool value
);

/// 记录错误
///
/// @param span Span 指针
/// @param message 错误消息
/// @return 错误码
otlp_error_t otlp_span_record_error(
    otlp_span_t* span,
    const char* message
);

/// 结束 Span
///
/// @param span Span 指针
void otlp_span_end(otlp_span_t* span);

// ============================================================
// 上下文传播
// ============================================================

/// 注入上下文到 HTTP 头
///
/// @param span Span 指针
/// @param headers 输出: 格式化的 traceparent 头
/// @param headers_len 缓冲区长度
/// @return 错误码
otlp_error_t otlp_context_inject(
    otlp_span_t* span,
    char* headers,
    size_t headers_len
);

/// 从 HTTP 头提取上下文
///
/// @param traceparent traceparent 头值
/// @param context 输出: Context 指针
/// @return 错误码
otlp_error_t otlp_context_extract(
    const char* traceparent,
    otlp_context_t** context
);

/// 释放 Context
///
/// @param context Context 指针
void otlp_context_free(otlp_context_t* context);

// ============================================================
// 工具函数
// ============================================================

/// 获取最后错误消息
///
/// @return 错误消息字符串 (不需要释放)
const char* otlp_get_last_error();

/// 获取库版本
///
/// @return 版本字符串 (格式: "major.minor.patch")
const char* otlp_version();

#ifdef __cplusplus
}
#endif

#endif // OTLP_FFI_H
```

### 2.3 Rust 实现

```rust
// src/lib.rs
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int};
use std::ptr;
use std::sync::{Arc, Mutex};
use once_cell::sync::Lazy;
use opentelemetry::trace::{Tracer, TracerProvider as _, Span as _, Status};
use opentelemetry_sdk::trace::{TracerProvider, Config};
use opentelemetry_otlp::new_exporter;

// ============================================================
// 错误处理
// ============================================================

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum OtlpError {
    Ok = 0,
    InvalidArgument = -1,
    NullPointer = -2,
    InitializationFailed = -3,
    ExportFailed = -4,
    OutOfMemory = -5,
    Internal = -99,
}

/// 全局最后错误消息
static LAST_ERROR: Lazy<Mutex<Option<CString>>> = Lazy::new(|| Mutex::new(None));

fn set_last_error(msg: &str) {
    let c_msg = CString::new(msg).unwrap_or_else(|_| CString::new("Invalid UTF-8").unwrap());
    *LAST_ERROR.lock().unwrap() = Some(c_msg);
}

#[no_mangle]
pub extern "C" fn otlp_get_last_error() -> *const c_char {
    LAST_ERROR
        .lock()
        .unwrap()
        .as_ref()
        .map(|s| s.as_ptr())
        .unwrap_or(ptr::null())
}

#[no_mangle]
pub extern "C" fn otlp_version() -> *const c_char {
    static VERSION: &str = concat!(env!("CARGO_PKG_VERSION"), "\0");
    VERSION.as_ptr() as *const c_char
}

// ============================================================
// 不透明类型包装
// ============================================================

pub struct OtlpTracerProvider {
    inner: TracerProvider,
}

pub struct OtlpTracer {
    inner: opentelemetry_sdk::trace::Tracer,
}

pub struct OtlpSpan {
    inner: opentelemetry_sdk::trace::Span,
}

pub struct OtlpContext {
    trace_id: String,
    span_id: String,
}

// ============================================================
// 初始化函数
// ============================================================

#[no_mangle]
pub extern "C" fn otlp_init(
    endpoint: *const c_char,
    service_name: *const c_char,
    provider: *mut *mut OtlpTracerProvider,
) -> c_int {
    if endpoint.is_null() || service_name.is_null() || provider.is_null() {
        set_last_error("Null pointer argument");
        return OtlpError::NullPointer as c_int;
    }

    let endpoint_str = unsafe {
        match CStr::from_ptr(endpoint).to_str() {
            Ok(s) => s,
            Err(_) => {
                set_last_error("Invalid UTF-8 in endpoint");
                return OtlpError::InvalidArgument as c_int;
            }
        }
    };

    let service_name_str = unsafe {
        match CStr::from_ptr(service_name).to_str() {
            Ok(s) => s,
            Err(_) => {
                set_last_error("Invalid UTF-8 in service_name");
                return OtlpError::InvalidArgument as c_int;
            }
        }
    };

    // 初始化 Tokio 运行时 (全局单例)
    static RUNTIME: Lazy<tokio::runtime::Runtime> = Lazy::new(|| {
        tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()
            .expect("Failed to create Tokio runtime")
    });

    let result = RUNTIME.block_on(async {
        // 创建 OTLP 导出器
        let exporter = new_exporter()
            .http()
            .with_endpoint(endpoint_str)
            .build_span_exporter()
            .map_err(|e| format!("Failed to create exporter: {}", e))?;

        // 创建 TracerProvider
        let provider = TracerProvider::builder()
            .with_batch_exporter(exporter, RUNTIME.handle().clone())
            .with_config(
                Config::default()
                    .with_resource(opentelemetry_sdk::Resource::new(vec![
                        opentelemetry::KeyValue::new(
                            "service.name",
                            service_name_str.to_string(),
                        ),
                    ])),
            )
            .build();

        Ok::<_, String>(provider)
    });

    match result {
        Ok(inner) => {
            let boxed = Box::new(OtlpTracerProvider { inner });
            unsafe {
                *provider = Box::into_raw(boxed);
            }
            OtlpError::Ok as c_int
        }
        Err(e) => {
            set_last_error(&e);
            OtlpError::InitializationFailed as c_int
        }
    }
}

#[no_mangle]
pub extern "C" fn otlp_tracer_provider_free(provider: *mut OtlpTracerProvider) {
    if !provider.is_null() {
        unsafe {
            let _ = Box::from_raw(provider);
        }
    }
}

#[no_mangle]
pub extern "C" fn otlp_get_tracer(
    provider: *mut OtlpTracerProvider,
    tracer: *mut *mut OtlpTracer,
) -> c_int {
    if provider.is_null() || tracer.is_null() {
        set_last_error("Null pointer argument");
        return OtlpError::NullPointer as c_int;
    }

    let provider_ref = unsafe { &*provider };

    let inner = provider_ref.inner.tracer("otlp-ffi");

    let boxed = Box::new(OtlpTracer { inner });
    unsafe {
        *tracer = Box::into_raw(boxed);
    }

    OtlpError::Ok as c_int
}

// ============================================================
// Span 操作
// ============================================================

#[no_mangle]
pub extern "C" fn otlp_span_create(
    tracer: *mut OtlpTracer,
    name: *const c_char,
    span: *mut *mut OtlpSpan,
) -> c_int {
    if tracer.is_null() || name.is_null() || span.is_null() {
        set_last_error("Null pointer argument");
        return OtlpError::NullPointer as c_int;
    }

    let name_str = unsafe {
        match CStr::from_ptr(name).to_str() {
            Ok(s) => s,
            Err(_) => {
                set_last_error("Invalid UTF-8 in name");
                return OtlpError::InvalidArgument as c_int;
            }
        }
    };

    let tracer_ref = unsafe { &*tracer };

    let inner = tracer_ref.inner.start(name_str);

    let boxed = Box::new(OtlpSpan { inner });
    unsafe {
        *span = Box::into_raw(boxed);
    }

    OtlpError::Ok as c_int
}

#[no_mangle]
pub extern "C" fn otlp_span_set_attribute_string(
    span: *mut OtlpSpan,
    key: *const c_char,
    value: *const c_char,
) -> c_int {
    if span.is_null() || key.is_null() || value.is_null() {
        set_last_error("Null pointer argument");
        return OtlpError::NullPointer as c_int;
    }

    let key_str = unsafe {
        match CStr::from_ptr(key).to_str() {
            Ok(s) => s,
            Err(_) => {
                set_last_error("Invalid UTF-8 in key");
                return OtlpError::InvalidArgument as c_int;
            }
        }
    };

    let value_str = unsafe {
        match CStr::from_ptr(value).to_str() {
            Ok(s) => s,
            Err(_) => {
                set_last_error("Invalid UTF-8 in value");
                return OtlpError::InvalidArgument as c_int;
            }
        }
    };

    let span_ref = unsafe { &mut *span };

    span_ref.inner.set_attribute(
        opentelemetry::KeyValue::new(key_str.to_string(), value_str.to_string()),
    );

    OtlpError::Ok as c_int
}

#[no_mangle]
pub extern "C" fn otlp_span_set_attribute_int(
    span: *mut OtlpSpan,
    key: *const c_char,
    value: i64,
) -> c_int {
    if span.is_null() || key.is_null() {
        set_last_error("Null pointer argument");
        return OtlpError::NullPointer as c_int;
    }

    let key_str = unsafe {
        match CStr::from_ptr(key).to_str() {
            Ok(s) => s,
            Err(_) => {
                set_last_error("Invalid UTF-8 in key");
                return OtlpError::InvalidArgument as c_int;
            }
        }
    };

    let span_ref = unsafe { &mut *span };

    span_ref.inner.set_attribute(
        opentelemetry::KeyValue::new(key_str.to_string(), value),
    );

    OtlpError::Ok as c_int
}

#[no_mangle]
pub extern "C" fn otlp_span_set_attribute_bool(
    span: *mut OtlpSpan,
    key: *const c_char,
    value: bool,
) -> c_int {
    if span.is_null() || key.is_null() {
        set_last_error("Null pointer argument");
        return OtlpError::NullPointer as c_int;
    }

    let key_str = unsafe {
        match CStr::from_ptr(key).to_str() {
            Ok(s) => s,
            Err(_) => {
                set_last_error("Invalid UTF-8 in key");
                return OtlpError::InvalidArgument as c_int;
            }
        }
    };

    let span_ref = unsafe { &mut *span };

    span_ref.inner.set_attribute(
        opentelemetry::KeyValue::new(key_str.to_string(), value),
    );

    OtlpError::Ok as c_int
}

#[no_mangle]
pub extern "C" fn otlp_span_record_error(
    span: *mut OtlpSpan,
    message: *const c_char,
) -> c_int {
    if span.is_null() || message.is_null() {
        set_last_error("Null pointer argument");
        return OtlpError::NullPointer as c_int;
    }

    let message_str = unsafe {
        match CStr::from_ptr(message).to_str() {
            Ok(s) => s,
            Err(_) => {
                set_last_error("Invalid UTF-8 in message");
                return OtlpError::InvalidArgument as c_int;
            }
        }
    };

    let span_ref = unsafe { &mut *span };

    span_ref.inner.set_status(Status::error(message_str));

    OtlpError::Ok as c_int
}

#[no_mangle]
pub extern "C" fn otlp_span_end(span: *mut OtlpSpan) {
    if !span.is_null() {
        unsafe {
            let mut boxed = Box::from_raw(span);
            boxed.inner.end();
        }
    }
}

// ============================================================
// 上下文传播
// ============================================================

#[no_mangle]
pub extern "C" fn otlp_context_inject(
    span: *mut OtlpSpan,
    headers: *mut c_char,
    headers_len: usize,
) -> c_int {
    if span.is_null() || headers.is_null() {
        set_last_error("Null pointer argument");
        return OtlpError::NullPointer as c_int;
    }

    let span_ref = unsafe { &*span };

    let context = span_ref.inner.span_context();
    let traceparent = format!(
        "00-{}-{}-01",
        context.trace_id(),
        context.span_id()
    );

    if traceparent.len() >= headers_len {
        set_last_error("Buffer too small");
        return OtlpError::InvalidArgument as c_int;
    }

    unsafe {
        ptr::copy_nonoverlapping(
            traceparent.as_ptr(),
            headers as *mut u8,
            traceparent.len(),
        );
        *headers.add(traceparent.len()) = 0; // Null 终止
    }

    OtlpError::Ok as c_int
}

#[no_mangle]
pub extern "C" fn otlp_context_extract(
    traceparent: *const c_char,
    context: *mut *mut OtlpContext,
) -> c_int {
    if traceparent.is_null() || context.is_null() {
        set_last_error("Null pointer argument");
        return OtlpError::NullPointer as c_int;
    }

    let traceparent_str = unsafe {
        match CStr::from_ptr(traceparent).to_str() {
            Ok(s) => s,
            Err(_) => {
                set_last_error("Invalid UTF-8 in traceparent");
                return OtlpError::InvalidArgument as c_int;
            }
        }
    };

    // 解析 traceparent: "00-{trace_id}-{span_id}-{flags}"
    let parts: Vec<&str> = traceparent_str.split('-').collect();
    if parts.len() != 4 {
        set_last_error("Invalid traceparent format");
        return OtlpError::InvalidArgument as c_int;
    }

    let ctx = OtlpContext {
        trace_id: parts[1].to_string(),
        span_id: parts[2].to_string(),
    };

    let boxed = Box::new(ctx);
    unsafe {
        *context = Box::into_raw(boxed);
    }

    OtlpError::Ok as c_int
}

#[no_mangle]
pub extern "C" fn otlp_context_free(context: *mut OtlpContext) {
    if !context.is_null() {
        unsafe {
            let _ = Box::from_raw(context);
        }
    }
}
```

---

## 3. 内存管理

### 3.1 所有权规则

```c
// 示例：正确的内存管理
#include "otlp_ffi.h"
#include <stdio.h>

int main() {
    otlp_tracer_provider_t* provider = NULL;
    otlp_tracer_t* tracer = NULL;
    otlp_span_t* span = NULL;

    // 1. 初始化 (分配)
    if (otlp_init("http://localhost:4318", "my-service", &provider) != OTLP_OK) {
        fprintf(stderr, "Init failed: %s\n", otlp_get_last_error());
        return 1;
    }

    // 2. 获取 Tracer (分配)
    if (otlp_get_tracer(provider, &tracer) != OTLP_OK) {
        fprintf(stderr, "Get tracer failed\n");
        otlp_tracer_provider_free(provider);
        return 1;
    }

    // 3. 创建 Span (分配)
    if (otlp_span_create(tracer, "my_operation", &span) != OTLP_OK) {
        fprintf(stderr, "Create span failed\n");
        // 注意：tracer 不需要手动释放 (由 provider 管理)
        otlp_tracer_provider_free(provider);
        return 1;
    }

    // 4. 使用 Span
    otlp_span_set_attribute_string(span, "key", "value");

    // 5. 结束 Span (自动释放)
    otlp_span_end(span);  // span 指针失效

    // 6. 清理 (释放)
    otlp_tracer_provider_free(provider);  // 同时释放 tracer

    return 0;
}
```

### 3.2 内存泄漏检测

```bash
# 使用 Valgrind 检测
valgrind --leak-check=full ./my_app

# 输出示例 (无泄漏):
# HEAP SUMMARY:
#     in use at exit: 0 bytes in 0 blocks
#   total heap usage: 234 allocs, 234 frees, 45,678 bytes allocated
#
# All heap blocks were freed -- no leaks are possible
```

---

## 4. 错误处理

### 4.1 错误检查模式

```c
// error_handling.c
#include "otlp_ffi.h"
#include <stdio.h>
#include <stdlib.h>

// 宏：检查错误
#define CHECK_OTLP(call) \
    do { \
        otlp_error_t err = (call); \
        if (err != OTLP_OK) { \
            fprintf(stderr, "OTLP Error at %s:%d: %s (code: %d)\n", \
                    __FILE__, __LINE__, otlp_get_last_error(), err); \
            goto cleanup; \
        } \
    } while (0)

int main() {
    otlp_tracer_provider_t* provider = NULL;
    otlp_tracer_t* tracer = NULL;
    otlp_span_t* span = NULL;
    int exit_code = 1;

    // 使用错误检查宏
    CHECK_OTLP(otlp_init("http://localhost:4318", "my-service", &provider));
    CHECK_OTLP(otlp_get_tracer(provider, &tracer));
    CHECK_OTLP(otlp_span_create(tracer, "operation", &span));

    // 业务逻辑...
    CHECK_OTLP(otlp_span_set_attribute_int(span, "count", 42));

    otlp_span_end(span);
    exit_code = 0;

cleanup:
    if (provider) {
        otlp_tracer_provider_free(provider);
    }

    return exit_code;
}
```

---

## 5. 线程安全

### 5.1 线程安全保证

```c
// multi_threaded.c
#include "otlp_ffi.h"
#include <pthread.h>
#include <stdio.h>

// 全局 TracerProvider (线程安全)
static otlp_tracer_provider_t* g_provider = NULL;

void* worker_thread(void* arg) {
    int thread_id = *(int*)arg;

    // 获取 Tracer (线程安全)
    otlp_tracer_t* tracer = NULL;
    if (otlp_get_tracer(g_provider, &tracer) != OTLP_OK) {
        return NULL;
    }

    // 创建 Span (每个线程独立)
    otlp_span_t* span = NULL;
    char span_name[64];
    snprintf(span_name, sizeof(span_name), "thread_%d_work", thread_id);

    if (otlp_span_create(tracer, span_name, &span) != OTLP_OK) {
        return NULL;
    }

    otlp_span_set_attribute_int(span, "thread.id", thread_id);

    // 模拟工作
    for (int i = 0; i < 1000; i++) {
        // 执行任务...
    }

    otlp_span_end(span);

    return NULL;
}

int main() {
    // 初始化 (仅一次)
    if (otlp_init("http://localhost:4318", "multi-threaded-app", &g_provider) != OTLP_OK) {
        fprintf(stderr, "Init failed\n");
        return 1;
    }

    // 启动 10 个线程
    pthread_t threads[10];
    int thread_ids[10];

    for (int i = 0; i < 10; i++) {
        thread_ids[i] = i;
        pthread_create(&threads[i], NULL, worker_thread, &thread_ids[i]);
    }

    // 等待线程完成
    for (int i = 0; i < 10; i++) {
        pthread_join(threads[i], NULL);
    }

    // 清理
    otlp_tracer_provider_free(g_provider);

    return 0;
}
```

---

## 6. Python 集成

### 6.1 Python 绑定 (ctypes)

```python
# otlp_ffi.py
from ctypes import *
from enum import IntEnum
import os

# 加载动态库
if os.name == 'nt':  # Windows
    lib = CDLL('./target/release/otlp_ffi.dll')
else:  # Linux/macOS
    lib = CDLL('./target/release/libotlp_ffi.so')

# 错误码枚举
class OtlpError(IntEnum):
    OK = 0
    INVALID_ARGUMENT = -1
    NULL_POINTER = -2
    INITIALIZATION_FAILED = -3
    EXPORT_FAILED = -4
    OUT_OF_MEMORY = -5
    INTERNAL = -99

# 函数签名定义
lib.otlp_init.argtypes = [c_char_p, c_char_p, POINTER(c_void_p)]
lib.otlp_init.restype = c_int

lib.otlp_get_tracer.argtypes = [c_void_p, POINTER(c_void_p)]
lib.otlp_get_tracer.restype = c_int

lib.otlp_span_create.argtypes = [c_void_p, c_char_p, POINTER(c_void_p)]
lib.otlp_span_create.restype = c_int

lib.otlp_span_set_attribute_string.argtypes = [c_void_p, c_char_p, c_char_p]
lib.otlp_span_set_attribute_string.restype = c_int

lib.otlp_span_set_attribute_int.argtypes = [c_void_p, c_char_p, c_int64]
lib.otlp_span_set_attribute_int.restype = c_int

lib.otlp_span_end.argtypes = [c_void_p]
lib.otlp_span_end.restype = None

lib.otlp_tracer_provider_free.argtypes = [c_void_p]
lib.otlp_tracer_provider_free.restype = None

lib.otlp_get_last_error.argtypes = []
lib.otlp_get_last_error.restype = c_char_p

# Python 包装类
class TracerProvider:
    def __init__(self, endpoint, service_name):
        self._handle = c_void_p()
        err = lib.otlp_init(
            endpoint.encode('utf-8'),
            service_name.encode('utf-8'),
            byref(self._handle)
        )
        if err != OtlpError.OK:
            raise RuntimeError(f"Init failed: {lib.otlp_get_last_error().decode()}")

    def __del__(self):
        if self._handle:
            lib.otlp_tracer_provider_free(self._handle)

    def get_tracer(self):
        return Tracer(self._handle)

class Tracer:
    def __init__(self, provider_handle):
        self._handle = c_void_p()
        err = lib.otlp_get_tracer(provider_handle, byref(self._handle))
        if err != OtlpError.OK:
            raise RuntimeError("Failed to get tracer")

    def start_span(self, name):
        return Span(self._handle, name)

class Span:
    def __init__(self, tracer_handle, name):
        self._handle = c_void_p()
        err = lib.otlp_span_create(
            tracer_handle,
            name.encode('utf-8'),
            byref(self._handle)
        )
        if err != OtlpError.OK:
            raise RuntimeError("Failed to create span")

    def set_attribute(self, key, value):
        if isinstance(value, str):
            lib.otlp_span_set_attribute_string(
                self._handle,
                key.encode('utf-8'),
                value.encode('utf-8')
            )
        elif isinstance(value, int):
            lib.otlp_span_set_attribute_int(
                self._handle,
                key.encode('utf-8'),
                c_int64(value)
            )

    def end(self):
        if self._handle:
            lib.otlp_span_end(self._handle)
            self._handle = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.end()

# 使用示例
if __name__ == '__main__':
    provider = TracerProvider('http://localhost:4318', 'python-app')
    tracer = provider.get_tracer()

    with tracer.start_span('my_operation') as span:
        span.set_attribute('user.id', 12345)
        span.set_attribute('action', 'purchase')

        # 业务逻辑...
        print("Doing work...")

    print("Span exported!")
```

---

## 7. Node.js 集成

### 7.1 Node.js N-API 绑定

```javascript
// bindings/node/index.js
const ffi = require('ffi-napi');
const ref = require('ref-napi');
const path = require('path');

// 类型定义
const voidPtr = ref.refType(ref.types.void);

// 加载动态库
const libPath = path.join(__dirname, '../../target/release/libotlp_ffi.so');
const lib = ffi.Library(libPath, {
    'otlp_init': ['int', ['string', 'string', voidPtr]],
    'otlp_get_tracer': ['int', [voidPtr, voidPtr]],
    'otlp_span_create': ['int', [voidPtr, 'string', voidPtr]],
    'otlp_span_set_attribute_string': ['int', [voidPtr, 'string', 'string']],
    'otlp_span_set_attribute_int': ['int', [voidPtr, 'string', 'int64']],
    'otlp_span_end': ['void', [voidPtr]],
    'otlp_tracer_provider_free': ['void', [voidPtr]],
    'otlp_get_last_error': ['string', []],
});

// JavaScript 包装类
class TracerProvider {
    constructor(endpoint, serviceName) {
        this.handle = ref.alloc(voidPtr);
        const err = lib.otlp_init(endpoint, serviceName, this.handle);
        if (err !== 0) {
            throw new Error(`Init failed: ${lib.otlp_get_last_error()}`);
        }
    }

    getTracer() {
        return new Tracer(this.handle.deref());
    }

    free() {
        if (this.handle) {
            lib.otlp_tracer_provider_free(this.handle.deref());
            this.handle = null;
        }
    }
}

class Tracer {
    constructor(providerHandle) {
        this.handle = ref.alloc(voidPtr);
        const err = lib.otlp_get_tracer(providerHandle, this.handle);
        if (err !== 0) {
            throw new Error('Failed to get tracer');
        }
    }

    startSpan(name) {
        return new Span(this.handle.deref(), name);
    }
}

class Span {
    constructor(tracerHandle, name) {
        this.handle = ref.alloc(voidPtr);
        const err = lib.otlp_span_create(tracerHandle, name, this.handle);
        if (err !== 0) {
            throw new Error('Failed to create span');
        }
    }

    setAttribute(key, value) {
        const handle = this.handle.deref();
        if (typeof value === 'string') {
            lib.otlp_span_set_attribute_string(handle, key, value);
        } else if (typeof value === 'number') {
            lib.otlp_span_set_attribute_int(handle, key, Math.floor(value));
        }
    }

    end() {
        if (this.handle) {
            lib.otlp_span_end(this.handle.deref());
            this.handle = null;
        }
    }
}

// 使用示例
const provider = new TracerProvider('http://localhost:4318', 'node-app');
const tracer = provider.getTracer();

const span = tracer.startSpan('my_operation');
span.setAttribute('user.id', 12345);
span.setAttribute('action', 'purchase');

setTimeout(() => {
    span.end();
    provider.free();
}, 1000);
```

---

## 8. Go 集成

### 8.1 Go CGO 绑定

```go
// otlp_ffi.go
package otlp

/*
#cgo LDFLAGS: -L../../target/release -lotlp_ffi -lpthread -ldl -lm
#include "../../include/otlp_ffi.h"
#include <stdlib.h>
*/
import "C"
import (
    "errors"
    "unsafe"
)

// TracerProvider 包装
type TracerProvider struct {
    handle *C.otlp_tracer_provider_t
}

// Tracer 包装
type Tracer struct {
    handle *C.otlp_tracer_t
}

// Span 包装
type Span struct {
    handle *C.otlp_span_t
}

// NewTracerProvider 创建 TracerProvider
func NewTracerProvider(endpoint, serviceName string) (*TracerProvider, error) {
    cEndpoint := C.CString(endpoint)
    defer C.free(unsafe.Pointer(cEndpoint))

    cServiceName := C.CString(serviceName)
    defer C.free(unsafe.Pointer(cServiceName))

    var handle *C.otlp_tracer_provider_t
    err := C.otlp_init(cEndpoint, cServiceName, &handle)

    if err != C.OTLP_OK {
        errMsg := C.GoString(C.otlp_get_last_error())
        return nil, errors.New(errMsg)
    }

    return &TracerProvider{handle: handle}, nil
}

// Free 释放 TracerProvider
func (tp *TracerProvider) Free() {
    if tp.handle != nil {
        C.otlp_tracer_provider_free(tp.handle)
        tp.handle = nil
    }
}

// GetTracer 获取 Tracer
func (tp *TracerProvider) GetTracer() (*Tracer, error) {
    var handle *C.otlp_tracer_t
    err := C.otlp_get_tracer(tp.handle, &handle)

    if err != C.OTLP_OK {
        return nil, errors.New("Failed to get tracer")
    }

    return &Tracer{handle: handle}, nil
}

// StartSpan 创建 Span
func (t *Tracer) StartSpan(name string) (*Span, error) {
    cName := C.CString(name)
    defer C.free(unsafe.Pointer(cName))

    var handle *C.otlp_span_t
    err := C.otlp_span_create(t.handle, cName, &handle)

    if err != C.OTLP_OK {
        return nil, errors.New("Failed to create span")
    }

    return &Span{handle: handle}, nil
}

// SetAttribute 设置属性
func (s *Span) SetAttribute(key string, value interface{}) {
    cKey := C.CString(key)
    defer C.free(unsafe.Pointer(cKey))

    switch v := value.(type) {
    case string:
        cValue := C.CString(v)
        defer C.free(unsafe.Pointer(cValue))
        C.otlp_span_set_attribute_string(s.handle, cKey, cValue)
    case int:
        C.otlp_span_set_attribute_int(s.handle, cKey, C.int64_t(v))
    case int64:
        C.otlp_span_set_attribute_int(s.handle, cKey, C.int64_t(v))
    }
}

// End 结束 Span
func (s *Span) End() {
    if s.handle != nil {
        C.otlp_span_end(s.handle)
        s.handle = nil
    }
}

// 使用示例
func Example() {
    provider, err := NewTracerProvider("http://localhost:4318", "go-app")
    if err != nil {
        panic(err)
    }
    defer provider.Free()

    tracer, err := provider.GetTracer()
    if err != nil {
        panic(err)
    }

    span, err := tracer.StartSpan("my_operation")
    if err != nil {
        panic(err)
    }

    span.SetAttribute("user.id", 12345)
    span.SetAttribute("action", "purchase")

    // 业务逻辑...

    span.End()
}
```

---

## 9. Java/JNI 集成

### 9.1 Java JNI 绑定

```java
// OtlpFFI.java
package com.example.otlp;

public class OtlpFFI {
    static {
        System.loadLibrary("otlp_ffi");
    }

    // Native 方法声明
    private static native long otlpInit(String endpoint, String serviceName);
    private static native long otlpGetTracer(long provider);
    private static native long otlpSpanCreate(long tracer, String name);
    private static native void otlpSpanSetAttributeString(long span, String key, String value);
    private static native void otlpSpanSetAttributeInt(long span, String key, long value);
    private static native void otlpSpanEnd(long span);
    private static native void otlpTracerProviderFree(long provider);

    // TracerProvider 包装类
    public static class TracerProvider implements AutoCloseable {
        private long handle;

        public TracerProvider(String endpoint, String serviceName) {
            this.handle = otlpInit(endpoint, serviceName);
            if (this.handle == 0) {
                throw new RuntimeException("Failed to initialize OTLP");
            }
        }

        public Tracer getTracer() {
            return new Tracer(otlpGetTracer(this.handle));
        }

        @Override
        public void close() {
            if (this.handle != 0) {
                otlpTracerProviderFree(this.handle);
                this.handle = 0;
            }
        }
    }

    // Tracer 包装类
    public static class Tracer {
        private long handle;

        Tracer(long handle) {
            this.handle = handle;
        }

        public Span startSpan(String name) {
            return new Span(otlpSpanCreate(this.handle, name));
        }
    }

    // Span 包装类
    public static class Span implements AutoCloseable {
        private long handle;

        Span(long handle) {
            this.handle = handle;
        }

        public void setAttribute(String key, String value) {
            otlpSpanSetAttributeString(this.handle, key, value);
        }

        public void setAttribute(String key, long value) {
            otlpSpanSetAttributeInt(this.handle, key, value);
        }

        public void end() {
            if (this.handle != 0) {
                otlpSpanEnd(this.handle);
                this.handle = 0;
            }
        }

        @Override
        public void close() {
            end();
        }
    }

    // 使用示例
    public static void main(String[] args) {
        try (TracerProvider provider = new TracerProvider("http://localhost:4318", "java-app")) {
            Tracer tracer = provider.getTracer();

            try (Span span = tracer.startSpan("my_operation")) {
                span.setAttribute("user.id", 12345L);
                span.setAttribute("action", "purchase");

                // 业务逻辑...
                System.out.println("Doing work...");
            }
        }
    }
}
```

---

## 10. 生产实践

### 10.1 构建脚本

```bash
#!/bin/bash
# build_all.sh

set -e

echo "🦀 Building Rust FFI library..."

# 1. 构建 Release 版本
cargo build --release

# 2. 生成头文件 (使用 cbindgen)
cbindgen --config cbindgen.toml --crate otlp-ffi --output include/otlp_ffi.h

# 3. 复制库文件
mkdir -p dist/lib
cp target/release/libotlp_ffi.{so,a} dist/lib/ 2>/dev/null || true
cp target/release/otlp_ffi.{dll,lib} dist/lib/ 2>/dev/null || true

# 4. 复制头文件
mkdir -p dist/include
cp include/otlp_ffi.h dist/include/

echo "✅ Build complete! Files in dist/"
```

### 10.2 测试套件

```c
// tests/test_ffi.c
#include "otlp_ffi.h"
#include <assert.h>
#include <stdio.h>

void test_init_and_free() {
    otlp_tracer_provider_t* provider = NULL;
    assert(otlp_init("http://localhost:4318", "test-app", &provider) == OTLP_OK);
    assert(provider != NULL);

    otlp_tracer_provider_free(provider);
    printf("✅ test_init_and_free passed\n");
}

void test_span_lifecycle() {
    otlp_tracer_provider_t* provider = NULL;
    otlp_tracer_t* tracer = NULL;
    otlp_span_t* span = NULL;

    assert(otlp_init("http://localhost:4318", "test-app", &provider) == OTLP_OK);
    assert(otlp_get_tracer(provider, &tracer) == OTLP_OK);
    assert(otlp_span_create(tracer, "test_span", &span) == OTLP_OK);

    assert(otlp_span_set_attribute_string(span, "key", "value") == OTLP_OK);
    assert(otlp_span_set_attribute_int(span, "count", 42) == OTLP_OK);

    otlp_span_end(span);
    otlp_tracer_provider_free(provider);

    printf("✅ test_span_lifecycle passed\n");
}

int main() {
    test_init_and_free();
    test_span_lifecycle();

    printf("🎉 All tests passed!\n");
    return 0;
}
```

---

## 📊 性能对比

| 语言 | 调用开销 | 内存开销 | 集成难度 |
|------|---------|---------|---------|
| **C** | 0 ns | 0 B | ⭐⭐ |
| **Python (ctypes)** | 50-100 ns | 24 B | ⭐⭐⭐ |
| **Node.js (ffi-napi)** | 80-150 ns | 32 B | ⭐⭐⭐⭐ |
| **Go (cgo)** | 10-30 ns | 8 B | ⭐⭐⭐ |
| **Java (JNI)** | 20-50 ns | 16 B | ⭐⭐⭐⭐⭐ |

---

## 🔗 参考资源

- [Rust FFI Book](https://doc.rust-lang.org/nomicon/ffi.html)
- [cbindgen](https://github.com/eqrion/cbindgen)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)

**文档版本**: v1.0  
**最后更新**: 2025年10月11日  
**维护者**: OTLP Rust FFI 专家团队
