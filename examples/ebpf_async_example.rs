//! eBPF 异步事件处理示例
//!
//! 演示如何使用异步事件处理器进行高并发事件处理

#[cfg(all(feature = "ebpf", target_os = "linux", feature = "async"))]
use otlp::ebpf::{AsyncEventProcessor, EbpfEvent, EbpfEventType};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    #[cfg(all(feature = "ebpf", target_os = "linux", feature = "async"))]
    {
        tracing_subscriber::fmt::init();

        println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        println!("eBPF 异步事件处理示例");
        println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        println!();

        // 1. 创建异步事件处理器
        println!("1. 创建异步事件处理器...");
        let processor = AsyncEventProcessor::with_batch_size(5000, 100);
        println!("   ✅ 异步事件处理器创建成功");
        println!("   - 最大缓冲区大小: 5000");
        println!("   - 批处理大小: 100");
        println!();

        // 2. 并发处理多个事件流
        println!("2. 并发处理多个事件流...");
        let mut handles = Vec::new();

        // 启动多个并发任务，每个任务处理不同类型的事件
        for task_id in 0..5 {
            let processor_clone = processor.clone();
            let handle = tokio::spawn(async move {
                for i in 0..100 {
                    let event = EbpfEvent {
                        event_type: match task_id % 3 {
                            0 => EbpfEventType::CpuSample,
                            1 => EbpfEventType::NetworkPacket,
                            _ => EbpfEventType::Syscall,
                        },
                        pid: 1000 + task_id,
                        tid: 2000 + (task_id * 100) + i,
                        timestamp: std::time::SystemTime::now(),
                        data: vec![0; 100],
                    };

                    processor_clone.process_event(event).await.unwrap();

                    // 模拟处理延迟
                    if i % 10 == 0 {
                        tokio::time::sleep(Duration::from_millis(1)).await;
                    }
                }
                task_id
            });
            handles.push(handle);
        }

        // 等待所有任务完成
        for handle in handles {
            let task_id = handle.await?;
            println!("   ✅ 任务 {} 完成", task_id);
        }
        println!();

        // 3. 检查事件数量
        println!("3. 检查事件数量...");
        let event_count = processor.event_count();
        println!("   ✅ 当前事件数: {}", event_count);
        println!();

        // 4. 批量刷新事件
        println!("4. 批量刷新事件...");
        let flushed_events = processor.flush_events_async().await?;
        println!("   ✅ 事件刷新成功");
        println!("   - 刷新事件数: {}", flushed_events.len());
        println!();

        // 5. 批量处理事件
        println!("5. 批量处理事件...");
        let mut batch = Vec::new();
        for i in 0..50 {
            batch.push(EbpfEvent {
                event_type: EbpfEventType::CpuSample,
                pid: 2000,
                tid: 3000 + i,
                timestamp: std::time::SystemTime::now(),
                data: vec![0; 50],
            });
        }
        processor.process_batch_async(batch).await?;
        println!("   ✅ 批量处理成功");
        println!("   - 当前事件数: {}", processor.event_count());
        println!();

        // 6. 清理
        println!("6. 清理资源...");
        processor.clear();
        println!("   ✅ 资源清理完成");
        println!();

        println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        println!("eBPF 异步事件处理示例完成！");
        println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux", feature = "async")))]
    {
        println!("此示例需要启用 ebpf 和 async feature，并在 Linux 平台上运行");
    }

    Ok(())
}
