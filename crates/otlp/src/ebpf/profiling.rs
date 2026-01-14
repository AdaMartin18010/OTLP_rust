//! CPU 性能分析
//!
//! 基于 eBPF 的 CPU 性能分析实现

use crate::error::Result;
use crate::ebpf::types::{EbpfConfig, EbpfEvent, EbpfEventType};
use crate::ebpf::loader::EbpfLoader;
use crate::profiling::types::PprofProfile;
use std::time::Duration;

/// eBPF CPU 性能分析器
pub struct EbpfCpuProfiler {
    config: EbpfConfig,
    loader: EbpfLoader,
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    started: bool,
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    start_time: Option<std::time::Instant>,
}

impl EbpfCpuProfiler {
    /// 创建新的 CPU 性能分析器
    pub fn new(config: EbpfConfig) -> Self {
        let loader = EbpfLoader::new(config.clone());
        Self {
            config,
            loader,
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            started: false,
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            start_time: None,
        }
    }

    /// 开始性能分析
    pub fn start(&mut self) -> Result<()> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            tracing::info!(
                "启动 eBPF CPU 性能分析，采样频率: {}Hz",
                self.config.sample_rate
            );

            // 注意: 实际的 CPU 性能分析实现需要:
            // 1. 加载 CPU 性能分析 eBPF 程序
            //    使用 aya crate:
            //       let mut bpf = Bpf::load(include_bytes!("cpu_profiler.bpf.o"))?;
            // 2. 附加到 perf events
            //    使用 perf_event_open 系统调用创建 perf event:
            //       let mut attr = PerfEventAttrBuilder::default()
            //           .ty(PerfTypeId::Software)
            //           .config(PerfSoftwareEvent::CpuClock as u64)
            //           .sample_period(1000000000 / self.config.sample_rate) // 转换为纳秒
            //           .sample_type(PerfSampleFlags::IP | PerfSampleFlags::TID | PerfSampleFlags::TIME)
            //           .build()?;
            //       let program: &mut PerfEvent = bpf.program_mut("cpu_profiler")?;
            //       program.load()?;
            //       program.attach_perf_event(attr)?;
            // 3. 开始采样（程序附加后自动开始）
            //    使用 Maps 存储采样数据:
            //       let stack_traces: HashMap<_, StackKey, u64> = HashMap::try_from(
            //           bpf.map_mut("stack_traces")?
            //       )?;

            self.started = true;
            self.start_time = Some(std::time::Instant::now());
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            tracing::warn!("eBPF 仅在 Linux 平台支持");
        }

        Ok(())
    }

    /// 停止性能分析并生成 profile
    pub fn stop(&mut self) -> Result<PprofProfile> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            if !self.started {
                return Err(crate::error::OtlpError::Processing(
                    crate::error::ProcessingError::InvalidState {
                        message: "性能分析器未启动".to_string(),
                    },
                ));
            }

            tracing::info!("停止 eBPF CPU 性能分析");

            // 注意: 实际的停止和 profile 生成实现需要:
            // 1. 停止采样（分离所有附加的 perf events）
            //    遍历所有程序并分离:
            //       for program in &mut bpf.programs_mut() {
            //           program.detach()?;
            //       }
            // 2. 从 eBPF Maps 收集采样数据
            //    使用 aya 的 Map 迭代器读取堆栈跟踪:
            //       let mut stack_traces = HashMap::new();
            //       let traces_map: HashMap<_, StackKey, u64> = HashMap::try_from(
            //           bpf.map("stack_traces")?
            //       )?;
            //       for item in traces_map.iter() {
            //           let (key, count) = item?;
            //           stack_traces.insert(key, count);
            //       }
            // 3. 转换为 pprof 格式
            //    解析堆栈地址，查找符号，创建 pprof Profile:
            //       let mut profile = PprofProfile::default();
            //       for (stack_key, count) in stack_traces {
            //           let mut sample = Sample::default();
            //           sample.value = vec![count as i64];
            //           for addr in stack_key.addresses {
            //               let location = resolve_address(addr)?;
            //               sample.location_id.push(location.id);
            //           }
            //           profile.sample.push(sample);
            //       }
            //    返回: Ok(profile)

            self.started = false;
            self.start_time = None;
        }

        // 注意: 实际实现需要完成以下步骤:
        // 1. 停止采样: 分离所有附加的 perf events
        //    for program in &mut bpf.programs_mut() {
        //        program.detach()?;
        //    }
        // 2. 从 eBPF Maps 收集采样数据
        //    let mut stack_traces = HashMap::new();
        //    let traces_map: HashMap<_, StackKey, u64> = HashMap::try_from(
        //        bpf.map("stack_traces")?
        //    )?;
        //    for item in traces_map.iter() {
        //        let (key, count) = item?;
        //        stack_traces.insert(key, count);
        //    }
        // 3. 转换为 pprof 格式
        //    let mut profile = PprofProfile::default();
        //    for (stack_key, count) in stack_traces {
        //        let mut sample = Sample::default();
        //        sample.value = vec![count as i64];
        //        for addr in stack_key.addresses {
        //            let location = resolve_address(addr)?;
        //            sample.location_id.push(location.id);
        //        }
        //        profile.sample.push(sample);
        //    }
        // 4. 返回完整的 profile
        //    Ok(profile)
        //
        // 当前返回空 profile 作为占位实现，实际使用时需要完成上述步骤
        Ok(PprofProfile::default())
    }

    /// 获取性能开销
    pub fn get_overhead(&self) -> crate::ebpf::types::EbpfOverheadMetrics {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            if self.started {
                // 读取 /proc/self/stat 获取 CPU 时间
                let cpu_time = match std::fs::read_to_string("/proc/self/stat") {
                    Ok(stat) => {
                        let fields: Vec<&str> = stat.split_whitespace().collect();
                        if fields.len() >= 15 {
                            let utime: u64 = fields[13].parse().unwrap_or(0);
                            let stime: u64 = fields[14].parse().unwrap_or(0);
                            // 转换为秒（假设 clock ticks = 100 Hz）
                            let clock_ticks_per_sec = 100;
                            (utime + stime) as f64 / clock_ticks_per_sec as f64
                        } else {
                            0.0
                        }
                    }
                    Err(e) => {
                        tracing::warn!("无法读取 /proc/self/stat: {}", e);
                        0.0
                    }
                };

                // 读取 /proc/self/status 获取内存使用
                let memory_bytes = match std::fs::read_to_string("/proc/self/status") {
                    Ok(status) => {
                        for line in status.lines() {
                            if line.starts_with("VmRSS:") {
                                if let Some(rss_kb_str) = line.split_whitespace().nth(1) {
                                    if let Ok(rss_kb) = rss_kb_str.parse::<usize>() {
                                        return crate::ebpf::types::EbpfOverheadMetrics {
                                            cpu_percent: cpu_time.min(100.0),
                                            memory_bytes: rss_kb * 1024,
                                            event_latency_us: 10, // 估算值，实际需要从事件中测量
                                        };
                                    }
                                }
                            }
                        }
                        0
                    }
                    Err(e) => {
                        tracing::warn!("无法读取 /proc/self/status: {}", e);
                        0
                    }
                };

                crate::ebpf::types::EbpfOverheadMetrics {
                    cpu_percent: cpu_time.min(100.0),
                    memory_bytes,
                    event_latency_us: 10, // 估算值
                }
            } else {
                crate::ebpf::types::EbpfOverheadMetrics::default()
            }
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            crate::ebpf::types::EbpfOverheadMetrics::default()
        }
    }

    /// 检查是否正在运行
    pub fn is_running(&self) -> bool {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            self.started
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            false
        }
    }

    /// 获取配置
    pub fn config(&self) -> &EbpfConfig {
        &self.config
    }

    /// 获取运行时长
    pub fn get_duration(&self) -> Option<Duration> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            self.start_time.map(|start| start.elapsed())
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            None
        }
    }

    /// 暂停性能分析（保持状态）
    pub fn pause(&mut self) -> Result<()> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            if !self.started {
                return Err(crate::error::OtlpError::Processing(
                    crate::error::ProcessingError::InvalidState {
                        message: "性能分析器未启动".to_string(),
                    }.into(),
                ));
            }

            tracing::info!("暂停 eBPF CPU 性能分析");
            // 注意: 实际的暂停实现需要:
            // 1. 暂停 perf event 采样
            //    使用 ioctl 系统调用禁用 perf event:
            //       use libc::{ioctl, PERF_EVENT_IOC_DISABLE, PERF_EVENT_IOC_ENABLE};
            //       ioctl(perf_fd, PERF_EVENT_IOC_DISABLE, 0)?;
            // 2. 或者通过 eBPF 程序内部标志控制采样
            //    使用 aya 的 Map API 更新控制标志:
            //       let control_map: HashMap<_, u32, u8> = HashMap::try_from(
            //           bpf.map_mut("control")?
            //       )?;
            //       control_map.insert(&0, &0, 0)?;  // 0 表示暂停
            Ok(())
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            Ok(())
        }
    }

    /// 恢复性能分析
    pub fn resume(&mut self) -> Result<()> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            if !self.started {
                return Err(crate::error::OtlpError::Processing(
                    crate::error::ProcessingError::InvalidState {
                        message: "性能分析器未启动".to_string(),
                    }.into(),
                ));
            }

            tracing::info!("恢复 eBPF CPU 性能分析");
            // 注意: 实际的恢复实现需要:
            // 1. 恢复 perf event 采样
            //    使用 ioctl 系统调用启用 perf event:
            //       use libc::{ioctl, PERF_EVENT_IOC_ENABLE};
            //       ioctl(perf_fd, PERF_EVENT_IOC_ENABLE, 0)?;
            // 2. 或者通过 eBPF 程序内部标志控制采样
            //    使用 aya 的 Map API 更新控制标志:
            //       let control_map: HashMap<_, u32, u8> = HashMap::try_from(
            //           bpf.map_mut("control")?
            //       )?;
            //       control_map.insert(&0, &1, 0)?;  // 1 表示恢复
            Ok(())
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            Ok(())
        }
    }
}
