//! # Host Semantic Conventions
//!
//! Implementation of OpenTelemetry Host Semantic Conventions v1.38.0
//! <https://opentelemetry.io/docs/specs/semconv/resource/host/>
//!
//! ## Features
//!
//! - **Host Identification**: Host name, ID, type, architecture
//! - **Operating System**: OS type, version, description
//! - **Hardware**: CPU, memory, disk information
//! - **Network**: IP addresses, MAC addresses
//!
//! ## Rust 1.92 Features
//!
//! - **Type-safe OS types**: Enum-based operating system definitions
//! - **Type-safe architectures**: Enum-based CPU architecture definitions
//! - **Builder pattern**: Ergonomic host attribute construction
//!
//! ## Usage Example
//!
//! ```rust
//! use otlp::semantic_conventions::host::{
//!     HostAttributesBuilder, OsType, HostArch,
//! };
//!
//! let attrs = HostAttributesBuilder::new()
//!     .name("web-server-01")
//!     .host_type("virtual-machine")
//!     .arch(HostArch::Amd64)
//!     .os_type(OsType::Linux)
//!     .os_version("5.15.0")
//!     .build()
//!     .unwrap();
//! ```

use super::common::{AttributeMap, AttributeValue, Result};
use std::collections::HashMap;
use std::net::IpAddr;

/// Operating system types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OsType {
    /// Windows
    Windows,
    /// Linux
    Linux,
    /// Darwin (macOS)
    Darwin,
    /// FreeBSD
    Freebsd,
    /// NetBSD
    Netbsd,
    /// OpenBSD
    Openbsd,
    /// DragonFly BSD
    Dragonflybsd,
    /// Solaris
    Solaris,
    /// AIX
    Aix,
    /// HP-UX
    Hpux,
    /// z/OS
    Zos,
    /// Other Unix
    Unix,
    /// Other
    Other,
}

impl OsType {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            OsType::Windows => "windows",
            OsType::Linux => "linux",
            OsType::Darwin => "darwin",
            OsType::Freebsd => "freebsd",
            OsType::Netbsd => "netbsd",
            OsType::Openbsd => "openbsd",
            OsType::Dragonflybsd => "dragonflybsd",
            OsType::Solaris => "solaris",
            OsType::Aix => "aix",
            OsType::Hpux => "hpux",
            OsType::Zos => "zos",
            OsType::Unix => "unix",
            OsType::Other => "other",
        }
    }

    /// Returns a user-friendly name
    pub fn display_name(&self) -> &'static str {
        match self {
            OsType::Windows => "Windows",
            OsType::Linux => "Linux",
            OsType::Darwin => "macOS",
            OsType::Freebsd => "FreeBSD",
            OsType::Netbsd => "NetBSD",
            OsType::Openbsd => "OpenBSD",
            OsType::Dragonflybsd => "DragonFly BSD",
            OsType::Solaris => "Solaris",
            OsType::Aix => "AIX",
            OsType::Hpux => "HP-UX",
            OsType::Zos => "z/OS",
            OsType::Unix => "Unix",
            OsType::Other => "Other",
        }
    }
}

impl std::fmt::Display for OsType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// CPU architectures
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostArch {
    /// x86 32-bit
    X86,
    /// x86-64 / AMD64
    Amd64,
    /// ARM 32-bit
    Arm32,
    /// ARM 64-bit / AArch64
    Aarch64,
    /// Itanium 64-bit
    Ia64,
    /// POWER 32-bit
    Ppc32,
    /// POWER 64-bit
    Ppc64,
    /// SPARC 32-bit
    Sparc32,
    /// SPARC 64-bit
    Sparc64,
    /// MIPS 32-bit
    Mips32,
    /// MIPS 64-bit
    Mips64,
    /// RISC-V 32-bit
    Riscv32,
    /// RISC-V 64-bit
    Riscv64,
    /// IBM Z (s390x)
    S390x,
    /// WebAssembly
    Wasm32,
    /// WebAssembly 64-bit
    Wasm64,
    /// Other
    Other,
}

impl HostArch {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            HostArch::X86 => "x86",
            HostArch::Amd64 => "amd64",
            HostArch::Arm32 => "arm32",
            HostArch::Aarch64 => "aarch64",
            HostArch::Ia64 => "ia64",
            HostArch::Ppc32 => "ppc32",
            HostArch::Ppc64 => "ppc64",
            HostArch::Sparc32 => "sparc32",
            HostArch::Sparc64 => "sparc64",
            HostArch::Mips32 => "mips32",
            HostArch::Mips64 => "mips64",
            HostArch::Riscv32 => "riscv32",
            HostArch::Riscv64 => "riscv64",
            HostArch::S390x => "s390x",
            HostArch::Wasm32 => "wasm32",
            HostArch::Wasm64 => "wasm64",
            HostArch::Other => "other",
        }
    }

    /// Returns whether this is a 64-bit architecture
    pub fn is_64bit(&self) -> bool {
        matches!(
            self,
            HostArch::Amd64
                | HostArch::Aarch64
                | HostArch::Ia64
                | HostArch::Ppc64
                | HostArch::Sparc64
                | HostArch::Mips64
                | HostArch::Riscv64
                | HostArch::S390x
                | HostArch::Wasm64
        )
    }

    /// Returns whether this is a 32-bit architecture
    pub fn is_32bit(&self) -> bool {
        !self.is_64bit()
    }
}

impl std::fmt::Display for HostArch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Host types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostType {
    /// Physical machine
    Physical,
    /// Virtual machine
    VirtualMachine,
    /// Container
    Container,
    /// Serverless function
    Serverless,
    /// Unknown
    Unknown,
}

impl HostType {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            HostType::Physical => "physical",
            HostType::VirtualMachine => "virtual-machine",
            HostType::Container => "container",
            HostType::Serverless => "serverless",
            HostType::Unknown => "unknown",
        }
    }
}

/// Device types for mobile/IoT
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeviceType {
    /// Desktop computer
    Desktop,
    /// Laptop computer
    Laptop,
    /// Mobile phone
    Mobile,
    /// Tablet device
    Tablet,
    /// IoT device
    Iot,
    /// Embedded device
    Embedded,
    /// Wearable device
    Wearable,
    /// TV or set-top box
    Tv,
    /// Gaming console
    Console,
    /// Other
    Other,
}

impl DeviceType {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            DeviceType::Desktop => "desktop",
            DeviceType::Laptop => "laptop",
            DeviceType::Mobile => "mobile",
            DeviceType::Tablet => "tablet",
            DeviceType::Iot => "iot",
            DeviceType::Embedded => "embedded",
            DeviceType::Wearable => "wearable",
            DeviceType::Tv => "tv",
            DeviceType::Console => "console",
            DeviceType::Other => "other",
        }
    }
}

/// Host attributes following OpenTelemetry semantic conventions
#[derive(Debug, Clone)]
pub struct HostAttributes {
    attributes: AttributeMap,
}

impl HostAttributes {
    /// Get all attributes as a map
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }

    /// Get a specific attribute
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.attributes.get(key)
    }
}

/// Builder for host attributes
#[derive(Debug, Default)]
pub struct HostAttributesBuilder {
    // Host identification
    name: Option<String>,
    host_id: Option<String>,
    host_type: Option<String>,
    host_type_enum: Option<HostType>,
    arch: Option<HostArch>,

    // Operating system
    os_type: Option<OsType>,
    os_version: Option<String>,
    os_name: Option<String>,
    os_description: Option<String>,
    os_build_id: Option<String>,

    // Kernel
    kernel_name: Option<String>,
    kernel_version: Option<String>,
    kernel_release: Option<String>,

    // Hardware
    cpu_vendor: Option<String>,
    cpu_family: Option<String>,
    cpu_model: Option<String>,
    cpu_stepping: Option<String>,
    cpu_cores: Option<i64>,
    cpu_count: Option<i64>,
    cpu_frequency_mhz: Option<f64>,
    cpu_cache_size_kb: Option<i64>,

    // Memory
    memory_total: Option<i64>,
    memory_swap_total: Option<i64>,

    // Boot
    boot_id: Option<String>,
    boot_time: Option<String>,

    // Virtualization
    hypervisor: Option<String>,

    // Device (for mobile/IoT)
    device_id: Option<String>,
    device_type: Option<DeviceType>,
    device_model: Option<String>,
    device_manufacturer: Option<String>,

    // Network
    ip_addresses: Vec<IpAddr>,
    mac_addresses: Vec<String>,

    // Custom attributes
    custom: HashMap<String, AttributeValue>,
}

impl HostAttributesBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self::default()
    }

    /// Set host name
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }

    /// Set host ID (unique identifier)
    pub fn host_id(mut self, id: impl Into<String>) -> Self {
        self.host_id = Some(id.into());
        self
    }

    /// Set host type as string
    pub fn host_type(mut self, host_type: impl Into<String>) -> Self {
        self.host_type = Some(host_type.into());
        self
    }

    /// Set host type using enum
    pub fn host_type_enum(mut self, host_type: HostType) -> Self {
        self.host_type_enum = Some(host_type);
        self
    }

    /// Set CPU architecture
    pub fn arch(mut self, arch: HostArch) -> Self {
        self.arch = Some(arch);
        self
    }

    /// Set OS type
    pub fn os_type(mut self, os_type: OsType) -> Self {
        self.os_type = Some(os_type);
        self
    }

    /// Set OS version
    pub fn os_version(mut self, version: impl Into<String>) -> Self {
        self.os_version = Some(version.into());
        self
    }

    /// Set OS name
    pub fn os_name(mut self, name: impl Into<String>) -> Self {
        self.os_name = Some(name.into());
        self
    }

    /// Set OS description
    pub fn os_description(mut self, desc: impl Into<String>) -> Self {
        self.os_description = Some(desc.into());
        self
    }

    /// Set OS build ID
    pub fn os_build_id(mut self, build_id: impl Into<String>) -> Self {
        self.os_build_id = Some(build_id.into());
        self
    }

    /// Set kernel name
    pub fn kernel_name(mut self, name: impl Into<String>) -> Self {
        self.kernel_name = Some(name.into());
        self
    }

    /// Set kernel version
    pub fn kernel_version(mut self, version: impl Into<String>) -> Self {
        self.kernel_version = Some(version.into());
        self
    }

    /// Set kernel release
    pub fn kernel_release(mut self, release: impl Into<String>) -> Self {
        self.kernel_release = Some(release.into());
        self
    }

    /// Set CPU vendor
    pub fn cpu_vendor(mut self, vendor: impl Into<String>) -> Self {
        self.cpu_vendor = Some(vendor.into());
        self
    }

    /// Set CPU family
    pub fn cpu_family(mut self, family: impl Into<String>) -> Self {
        self.cpu_family = Some(family.into());
        self
    }

    /// Set CPU model
    pub fn cpu_model(mut self, model: impl Into<String>) -> Self {
        self.cpu_model = Some(model.into());
        self
    }

    /// Set CPU stepping
    pub fn cpu_stepping(mut self, stepping: impl Into<String>) -> Self {
        self.cpu_stepping = Some(stepping.into());
        self
    }

    /// Set number of CPU cores
    pub fn cpu_cores(mut self, cores: i64) -> Self {
        self.cpu_cores = Some(cores);
        self
    }

    /// Set number of physical CPUs
    pub fn cpu_count(mut self, count: i64) -> Self {
        self.cpu_count = Some(count);
        self
    }

    /// Set CPU frequency in MHz
    pub fn cpu_frequency_mhz(mut self, freq: f64) -> Self {
        self.cpu_frequency_mhz = Some(freq);
        self
    }

    /// Set CPU cache size in KB
    pub fn cpu_cache_size_kb(mut self, size: i64) -> Self {
        self.cpu_cache_size_kb = Some(size);
        self
    }

    /// Set total memory in bytes
    pub fn memory_total(mut self, bytes: i64) -> Self {
        self.memory_total = Some(bytes);
        self
    }

    /// Set total swap memory in bytes
    pub fn memory_swap_total(mut self, bytes: i64) -> Self {
        self.memory_swap_total = Some(bytes);
        self
    }

    /// Set boot ID
    pub fn boot_id(mut self, id: impl Into<String>) -> Self {
        self.boot_id = Some(id.into());
        self
    }

    /// Set boot time (ISO 8601 format recommended)
    pub fn boot_time(mut self, time: impl Into<String>) -> Self {
        self.boot_time = Some(time.into());
        self
    }

    /// Set hypervisor name
    pub fn hypervisor(mut self, hypervisor: impl Into<String>) -> Self {
        self.hypervisor = Some(hypervisor.into());
        self
    }

    /// Set device ID
    pub fn device_id(mut self, id: impl Into<String>) -> Self {
        self.device_id = Some(id.into());
        self
    }

    /// Set device type
    pub fn device_type(mut self, device_type: DeviceType) -> Self {
        self.device_type = Some(device_type);
        self
    }

    /// Set device model
    pub fn device_model(mut self, model: impl Into<String>) -> Self {
        self.device_model = Some(model.into());
        self
    }

    /// Set device manufacturer
    pub fn device_manufacturer(mut self, manufacturer: impl Into<String>) -> Self {
        self.device_manufacturer = Some(manufacturer.into());
        self
    }

    /// Add IP address
    pub fn add_ip_address(mut self, addr: IpAddr) -> Self {
        self.ip_addresses.push(addr);
        self
    }

    /// Set IP addresses
    pub fn ip_addresses(mut self, addrs: Vec<IpAddr>) -> Self {
        self.ip_addresses = addrs;
        self
    }

    /// Add MAC address
    pub fn add_mac_address(mut self, mac: impl Into<String>) -> Self {
        self.mac_addresses.push(mac.into());
        self
    }

    /// Set MAC addresses
    pub fn mac_addresses(mut self, macs: Vec<String>) -> Self {
        self.mac_addresses = macs;
        self
    }

    /// Add a custom attribute
    pub fn custom_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.custom.insert(key.into(), value);
        self
    }

    /// Build the host attributes
    pub fn build(self) -> Result<HostAttributes> {
        let mut attributes = AttributeMap::new();

        // Host identification
        if let Some(name) = self.name {
            attributes.insert("host.name".to_string(), AttributeValue::String(name));
        }

        if let Some(id) = self.host_id {
            attributes.insert("host.id".to_string(), AttributeValue::String(id));
        }

        if let Some(host_type) = self.host_type {
            attributes.insert("host.type".to_string(), AttributeValue::String(host_type));
        } else if let Some(host_type) = self.host_type_enum {
            attributes.insert(
                "host.type".to_string(),
                AttributeValue::String(host_type.as_str().to_string()),
            );
        }

        if let Some(arch) = self.arch {
            attributes.insert(
                "host.arch".to_string(),
                AttributeValue::String(arch.as_str().to_string()),
            );
        }

        // Operating system
        if let Some(os_type) = self.os_type {
            attributes.insert(
                "os.type".to_string(),
                AttributeValue::String(os_type.as_str().to_string()),
            );
            // Also add display name
            attributes.insert(
                "os.type.name".to_string(),
                AttributeValue::String(os_type.display_name().to_string()),
            );
        }

        if let Some(version) = self.os_version {
            attributes.insert("os.version".to_string(), AttributeValue::String(version));
        }

        if let Some(name) = self.os_name {
            attributes.insert("os.name".to_string(), AttributeValue::String(name));
        }

        if let Some(desc) = self.os_description {
            attributes.insert("os.description".to_string(), AttributeValue::String(desc));
        }

        if let Some(build_id) = self.os_build_id {
            attributes.insert("os.build_id".to_string(), AttributeValue::String(build_id));
        }

        // Kernel
        if let Some(name) = self.kernel_name {
            attributes.insert("host.kernel.name".to_string(), AttributeValue::String(name));
        }

        if let Some(version) = self.kernel_version {
            attributes.insert(
                "host.kernel.version".to_string(),
                AttributeValue::String(version),
            );
        }

        if let Some(release) = self.kernel_release {
            attributes.insert(
                "host.kernel.release".to_string(),
                AttributeValue::String(release),
            );
        }

        // CPU
        if let Some(vendor) = self.cpu_vendor {
            attributes.insert(
                "host.cpu.vendor.id".to_string(),
                AttributeValue::String(vendor),
            );
        }

        if let Some(family) = self.cpu_family {
            attributes.insert(
                "host.cpu.family".to_string(),
                AttributeValue::String(family),
            );
        }

        if let Some(model) = self.cpu_model {
            attributes.insert(
                "host.cpu.model.name".to_string(),
                AttributeValue::String(model),
            );
        }

        if let Some(stepping) = self.cpu_stepping {
            attributes.insert(
                "host.cpu.stepping".to_string(),
                AttributeValue::String(stepping),
            );
        }

        if let Some(cores) = self.cpu_cores {
            attributes.insert("host.cpu.cores".to_string(), AttributeValue::Int(cores));
        }

        if let Some(count) = self.cpu_count {
            attributes.insert("host.cpu.count".to_string(), AttributeValue::Int(count));
        }

        if let Some(freq) = self.cpu_frequency_mhz {
            attributes.insert(
                "host.cpu.frequency.mhz".to_string(),
                AttributeValue::Double(freq),
            );
        }

        if let Some(cache) = self.cpu_cache_size_kb {
            attributes.insert(
                "host.cpu.cache.size.kb".to_string(),
                AttributeValue::Int(cache),
            );
        }

        // Memory
        if let Some(total) = self.memory_total {
            attributes.insert("host.memory.total".to_string(), AttributeValue::Int(total));
        }

        if let Some(swap) = self.memory_swap_total {
            attributes.insert(
                "host.memory.swap.total".to_string(),
                AttributeValue::Int(swap),
            );
        }

        // Boot
        if let Some(id) = self.boot_id {
            attributes.insert("host.boot.id".to_string(), AttributeValue::String(id));
        }

        if let Some(time) = self.boot_time {
            attributes.insert("host.boot.time".to_string(), AttributeValue::String(time));
        }

        // Virtualization
        if let Some(hypervisor) = self.hypervisor {
            attributes.insert(
                "host.hypervisor".to_string(),
                AttributeValue::String(hypervisor),
            );
        }

        // Device
        if let Some(id) = self.device_id {
            attributes.insert("device.id".to_string(), AttributeValue::String(id));
        }

        if let Some(device_type) = self.device_type {
            attributes.insert(
                "device.type".to_string(),
                AttributeValue::String(device_type.as_str().to_string()),
            );
        }

        if let Some(model) = self.device_model {
            attributes.insert("device.model".to_string(), AttributeValue::String(model));
        }

        if let Some(manufacturer) = self.device_manufacturer {
            attributes.insert(
                "device.manufacturer".to_string(),
                AttributeValue::String(manufacturer),
            );
        }

        // Network
        if !self.ip_addresses.is_empty() {
            let ips: Vec<AttributeValue> = self
                .ip_addresses
                .into_iter()
                .map(|ip| AttributeValue::String(ip.to_string()))
                .collect();
            attributes.insert("host.ip".to_string(), AttributeValue::Array(ips));
        }

        if !self.mac_addresses.is_empty() {
            let macs: Vec<AttributeValue> = self
                .mac_addresses
                .into_iter()
                .map(AttributeValue::String)
                .collect();
            attributes.insert("host.mac".to_string(), AttributeValue::Array(macs));
        }

        // Add custom attributes
        attributes.extend(self.custom);

        Ok(HostAttributes { attributes })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{Ipv4Addr, Ipv6Addr};

    #[test]
    fn test_os_type() {
        assert_eq!(OsType::Linux.as_str(), "linux");
        assert_eq!(OsType::Windows.as_str(), "windows");
        assert_eq!(OsType::Darwin.as_str(), "darwin");
        assert_eq!(OsType::Darwin.display_name(), "macOS");
    }

    #[test]
    fn test_host_arch() {
        assert_eq!(HostArch::Amd64.as_str(), "amd64");
        assert_eq!(HostArch::Aarch64.as_str(), "aarch64");
        assert_eq!(HostArch::X86.as_str(), "x86");
        assert!(HostArch::Amd64.is_64bit());
        assert!(HostArch::X86.is_32bit());
    }

    #[test]
    fn test_host_type() {
        assert_eq!(HostType::VirtualMachine.as_str(), "virtual-machine");
        assert_eq!(HostType::Container.as_str(), "container");
        assert_eq!(HostType::Physical.as_str(), "physical");
    }

    #[test]
    fn test_device_type() {
        assert_eq!(DeviceType::Mobile.as_str(), "mobile");
        assert_eq!(DeviceType::Desktop.as_str(), "desktop");
        assert_eq!(DeviceType::Iot.as_str(), "iot");
    }

    #[test]
    fn test_host_attributes_builder_minimal() {
        let attrs = HostAttributesBuilder::new().build().unwrap();
        assert!(attrs.as_map().is_empty());
    }

    #[test]
    fn test_host_attributes_builder_full() {
        let attrs = HostAttributesBuilder::new()
            .name("web-server-01")
            .host_id("host-abc-123")
            .host_type_enum(HostType::VirtualMachine)
            .arch(HostArch::Amd64)
            .os_type(OsType::Linux)
            .os_version("5.15.0-105-generic")
            .os_name("Ubuntu 22.04.3 LTS")
            .kernel_name("Linux")
            .kernel_release("5.15.0-105-generic")
            .cpu_cores(8)
            .cpu_count(1)
            .memory_total(17179869184)
            .hypervisor("VMware")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("host.name"),
            Some(&AttributeValue::String("web-server-01".to_string()))
        );
        assert_eq!(
            attrs.get("host.id"),
            Some(&AttributeValue::String("host-abc-123".to_string()))
        );
        assert_eq!(
            attrs.get("host.type"),
            Some(&AttributeValue::String("virtual-machine".to_string()))
        );
        assert_eq!(
            attrs.get("host.arch"),
            Some(&AttributeValue::String("amd64".to_string()))
        );
        assert_eq!(
            attrs.get("os.type"),
            Some(&AttributeValue::String("linux".to_string()))
        );
        assert_eq!(
            attrs.get("os.version"),
            Some(&AttributeValue::String("5.15.0-105-generic".to_string()))
        );
        assert_eq!(attrs.get("host.cpu.cores"), Some(&AttributeValue::Int(8)));
        assert_eq!(
            attrs.get("host.hypervisor"),
            Some(&AttributeValue::String("VMware".to_string()))
        );
    }

    #[test]
    fn test_host_ip_addresses() {
        let attrs = HostAttributesBuilder::new()
            .name("multi-homed-host")
            .add_ip_address(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 100)))
            .add_ip_address(IpAddr::V6(Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 1)))
            .build()
            .unwrap();

        let ips = attrs.get("host.ip");
        assert!(ips.is_some());
        if let Some(AttributeValue::Array(arr)) = ips {
            assert_eq!(arr.len(), 2);
        }
    }

    #[test]
    fn test_host_mac_addresses() {
        let attrs = HostAttributesBuilder::new()
            .name("networked-host")
            .add_mac_address("aa:bb:cc:dd:ee:ff")
            .add_mac_address("11:22:33:44:55:66")
            .build()
            .unwrap();

        let macs = attrs.get("host.mac");
        assert!(macs.is_some());
        if let Some(AttributeValue::Array(arr)) = macs {
            assert_eq!(arr.len(), 2);
            assert_eq!(
                arr[0],
                AttributeValue::String("aa:bb:cc:dd:ee:ff".to_string())
            );
        }
    }

    #[test]
    fn test_host_device_attributes() {
        let attrs = HostAttributesBuilder::new()
            .device_id("device-123")
            .device_type(DeviceType::Mobile)
            .device_model("iPhone14,2")
            .device_manufacturer("Apple")
            .arch(HostArch::Aarch64)
            .os_type(OsType::Darwin)
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("device.id"),
            Some(&AttributeValue::String("device-123".to_string()))
        );
        assert_eq!(
            attrs.get("device.type"),
            Some(&AttributeValue::String("mobile".to_string()))
        );
        assert_eq!(
            attrs.get("device.model"),
            Some(&AttributeValue::String("iPhone14,2".to_string()))
        );
        assert_eq!(
            attrs.get("device.manufacturer"),
            Some(&AttributeValue::String("Apple".to_string()))
        );
    }

    #[test]
    fn test_host_boot_info() {
        let attrs = HostAttributesBuilder::new()
            .name("booted-host")
            .boot_id("boot-xyz-789")
            .boot_time("2024-01-15T08:30:00Z")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("host.boot.id"),
            Some(&AttributeValue::String("boot-xyz-789".to_string()))
        );
        assert_eq!(
            attrs.get("host.boot.time"),
            Some(&AttributeValue::String("2024-01-15T08:30:00Z".to_string()))
        );
    }

    #[test]
    fn test_host_cpu_details() {
        let attrs = HostAttributesBuilder::new()
            .name("cpu-host")
            .cpu_vendor("GenuineIntel")
            .cpu_family("6")
            .cpu_model("Intel Core i7")
            .cpu_stepping("2")
            .cpu_frequency_mhz(3200.0)
            .cpu_cache_size_kb(12288)
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("host.cpu.vendor.id"),
            Some(&AttributeValue::String("GenuineIntel".to_string()))
        );
        assert_eq!(
            attrs.get("host.cpu.frequency.mhz"),
            Some(&AttributeValue::Double(3200.0))
        );
        assert_eq!(
            attrs.get("host.cpu.cache.size.kb"),
            Some(&AttributeValue::Int(12288))
        );
    }

    #[test]
    fn test_host_custom_attributes() {
        let attrs = HostAttributesBuilder::new()
            .name("custom-host")
            .custom_attribute(
                "custom.datacenter",
                AttributeValue::String("us-west-1".to_string()),
            )
            .custom_attribute("custom.rack", AttributeValue::Int(42))
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("custom.datacenter"),
            Some(&AttributeValue::String("us-west-1".to_string()))
        );
        assert_eq!(attrs.get("custom.rack"), Some(&AttributeValue::Int(42)));
    }

    #[test]
    fn test_all_architectures() {
        let arches = vec![
            HostArch::X86,
            HostArch::Amd64,
            HostArch::Arm32,
            HostArch::Aarch64,
            HostArch::Ppc64,
            HostArch::S390x,
        ];

        for arch in arches {
            let attrs = HostAttributesBuilder::new()
                .name("test-host")
                .arch(arch)
                .build()
                .unwrap();

            assert!(
                attrs.get("host.arch").is_some(),
                "host.arch should be present for {:?}",
                arch
            );
        }
    }

    #[test]
    fn test_all_os_types() {
        let os_types = vec![
            OsType::Linux,
            OsType::Windows,
            OsType::Darwin,
            OsType::Freebsd,
            OsType::Solaris,
        ];

        for os_type in os_types {
            let attrs = HostAttributesBuilder::new()
                .name("test-host")
                .os_type(os_type)
                .build()
                .unwrap();

            assert!(
                attrs.get("os.type").is_some(),
                "os.type should be present for {:?}",
                os_type
            );
        }
    }
}
