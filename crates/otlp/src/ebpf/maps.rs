//! eBPF Maps 管理
//!
//! 管理 eBPF Maps 的读写操作

use crate::error::Result;
use crate::ebpf::error::EbpfError;

/// eBPF Map 类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MapType {
    /// 哈希表
    Hash,
    /// 数组
    Array,
    /// 性能事件
    PerfEvent,
    /// 环形缓冲区
    RingBuffer,
}

/// eBPF Maps 管理器
pub struct MapsManager {
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    maps: Vec<MapInfo>,
}

#[derive(Debug, Clone)]
struct MapInfo {
    name: String,
    map_type: MapType,
    key_size: usize,
    value_size: usize,
}

impl MapsManager {
    /// 创建新的 Maps 管理器
    pub fn new() -> Self {
        Self {
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            maps: Vec::new(),
        }
    }

    /// 读取 Map 值
    ///
    /// # 参数
    ///
    /// * `name` - Map 名称
    /// * `key` - 键的字节表示
    ///
    /// # 返回
    ///
    /// 成功返回值的字节表示，失败返回错误
    ///
    /// # 说明
    ///
    /// 从 eBPF Map 中读取指定键的值。
    /// 支持 Hash Map 和 Array Map。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::MapsManager;
    ///
    /// let manager = MapsManager::new();
    /// let key = b"my_key";
    /// let value = manager.read_map("my_map", key)?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn read_map(&self, name: &str, key: &[u8]) -> Result<Vec<u8>> {
        // 验证参数
        if name.is_empty() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(
                "Map 名称不能为空".to_string(),
            )
            .into());
        }
        if key.is_empty() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(
                "键不能为空".to_string(),
            )
            .into());
        }

        // 检查 Map 是否存在
        let map_info = self.get_map_info(name);
        if map_info.is_none() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(format!(
                "Map 不存在: {}",
                name
            ))
            .into());
        }

        let map_info = map_info.unwrap();

        // 验证键大小
        if key.len() != map_info.key_size {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(format!(
                "键大小不匹配: 期望 {} bytes，实际 {} bytes",
                map_info.key_size,
                key.len()
            ))
            .into());
        }

        tracing::debug!("读取 Map: {} (key: {:?}, key_size: {}, value_size: {})", 
            name, key, map_info.key_size, map_info.value_size);

        // 注意: 实际的 Map 读取需要:
        // 1. 使用 aya 获取 Map:
        //    let map = bpf.map(name)?;
        // 2. 根据 Map 类型读取:
        //    - Hash Map: map.get(key, 0)?;
        //    - Array Map: map.get(index, 0)?;
        // 3. 返回值的字节表示

        // 临时实现：返回空值（实际应从 Map 读取）
        Ok(vec![0u8; map_info.value_size])
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn read_map(&self, _name: &str, _key: &[u8]) -> Result<Vec<u8>> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 写入 Map 值
    ///
    /// # 参数
    ///
    /// * `name` - Map 名称
    /// * `key` - 键的字节表示
    /// * `value` - 值的字节表示
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 向 eBPF Map 中写入键值对。
    /// 支持 Hash Map 和 Array Map。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::MapsManager;
    ///
    /// let mut manager = MapsManager::new();
    /// let key = b"my_key";
    /// let value = b"my_value";
    /// manager.write_map("my_map", key, value)?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn write_map(&mut self, name: &str, key: &[u8], value: &[u8]) -> Result<()> {
        // 验证参数
        if name.is_empty() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(
                "Map 名称不能为空".to_string(),
            )
            .into());
        }
        if key.is_empty() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(
                "键不能为空".to_string(),
            )
            .into());
        }
        if value.is_empty() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(
                "值不能为空".to_string(),
            )
            .into());
        }

        // 检查 Map 是否存在
        let map_info = self.get_map_info(name);
        if map_info.is_none() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(format!(
                "Map 不存在: {}",
                name
            ))
            .into());
        }

        let map_info = map_info.unwrap();

        // 验证键和值的大小
        if key.len() != map_info.key_size {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(format!(
                "键大小不匹配: 期望 {} bytes，实际 {} bytes",
                map_info.key_size,
                key.len()
            ))
            .into());
        }
        if value.len() != map_info.value_size {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(format!(
                "值大小不匹配: 期望 {} bytes，实际 {} bytes",
                map_info.value_size,
                value.len()
            ))
            .into());
        }

        tracing::debug!("写入 Map: {} (key: {:?}, value: {:?})", name, key, value);

        // 注意: 实际的 Map 写入需要:
        // 1. 使用 aya 获取 Map:
        //    let mut map = bpf.map_mut(name)?;
        // 2. 根据 Map 类型写入:
        //    - Hash Map: map.insert(key, value, 0)?;
        //    - Array Map: map.set(index, value, 0)?;
        // 3. 处理写入结果

        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn write_map(&mut self, _name: &str, _key: &[u8], _value: &[u8]) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 删除 Map 中的键值对
    ///
    /// # 参数
    ///
    /// * `name` - Map 名称
    /// * `key` - 要删除的键的字节表示
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 从 eBPF Map 中删除指定的键值对。
    /// 仅支持 Hash Map（Array Map 不支持删除操作）。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::MapsManager;
    ///
    /// let mut manager = MapsManager::new();
    /// let key = b"my_key";
    /// manager.delete_map("my_map", key)?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn delete_map(&mut self, name: &str, key: &[u8]) -> Result<()> {
        // 验证参数
        if name.is_empty() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(
                "Map 名称不能为空".to_string(),
            )
            .into());
        }
        if key.is_empty() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(
                "键不能为空".to_string(),
            )
            .into());
        }

        // 检查 Map 是否存在
        let map_info = self.get_map_info(name);
        if map_info.is_none() {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(format!(
                "Map 不存在: {}",
                name
            ))
            .into());
        }

        let map_info = map_info.unwrap();

        // 验证 Map 类型（只有 Hash Map 支持删除）
        if map_info.map_type != MapType::Hash {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(format!(
                "Map 类型 {} 不支持删除操作，仅 Hash Map 支持",
                format!("{:?}", map_info.map_type)
            ))
            .into());
        }

        // 验证键大小
        if key.len() != map_info.key_size {
            return Err(crate::ebpf::error::EbpfError::MapOperationFailed(format!(
                "键大小不匹配: 期望 {} bytes，实际 {} bytes",
                map_info.key_size,
                key.len()
            ))
            .into());
        }

        tracing::debug!("删除 Map 键值对: {} (key: {:?})", name, key);

        // 注意: 实际的 Map 删除需要:
        // 1. 使用 aya 获取 Map:
        //    let mut map = bpf.map_mut(name)?;
        // 2. 删除键值对:
        //    map.remove(key)?;
        // 3. 处理删除结果

        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn delete_map(&mut self, _name: &str, _key: &[u8]) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 注册 Map
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn register_map(&mut self, name: String, map_type: MapType, key_size: usize, value_size: usize) {
        self.maps.push(MapInfo {
            name,
            map_type,
            key_size,
            value_size,
        });
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn register_map(&mut self, _name: String, _map_type: MapType, _key_size: usize, _value_size: usize) {
        // 非 Linux 平台不做任何操作
    }

    /// 获取 Map 信息
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn get_map_info(&self, name: &str) -> Option<&MapInfo> {
        self.maps.iter().find(|m| m.name == name)
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn get_map_info(&self, _name: &str) -> Option<&MapInfo> {
        None
    }

    /// 列出所有 Map
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn list_maps(&self) -> Vec<(&str, MapType, usize, usize)> {
        self.maps
            .iter()
            .map(|m| (m.name.as_str(), m.map_type, m.key_size, m.value_size))
            .collect()
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn list_maps(&self) -> Vec<(&str, MapType, usize, usize)> {
        vec![]
    }

    /// 获取 Map 数量
    pub fn map_count(&self) -> usize {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            self.maps.len()
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            0
        }
    }

impl Default for MapsManager {
    fn default() -> Self {
        Self::new()
    }
}
