//! # Process Semantic Conventions
//!
//! Implementation of OpenTelemetry Process Semantic Conventions v1.38.0
//! <https://opentelemetry.io/docs/specs/semconv/resource/process/>
//!
//! ## Features
//!
//! - **Process Information**: PID, command, owner, executable path
//! - **Runtime Details**: Runtime name, version, description
//! - **Parent Process**: Parent PID relationship
//! - **Command Line**: Arguments and full command line
//!
//! ## Rust 1.92 Features
//!
//! - **Type-safe runtimes**: Enum-based runtime definitions
//! - **Builder pattern**: Ergonomic process attribute construction
//! - **Process hierarchy**: Parent-child relationship tracking
//!
//! ## Usage Example
//!
//! ```rust
//! use otlp::semantic_conventions::process::{
//!     ProcessAttributesBuilder, ProcessRuntime,
//! };
//!
//! let attrs = ProcessAttributesBuilder::new()
//!     .pid(1234)
//!     .command("my-app")
//!     .runtime(ProcessRuntime::Rust)
//!     .runtime_version("1.75.0")
//!     .build()
//!     .unwrap();
//! ```

use super::common::{AttributeMap, AttributeValue, Result};
use std::collections::HashMap;

/// Process runtimes/languages
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcessRuntime {
    /// Rust
    Rust,
    /// Go
    Go,
    /// Java
    Java,
    /// Node.js (JavaScript/TypeScript)
    Nodejs,
    /// Python
    Python,
    /// .NET
    Dotnet,
    /// Ruby
    Ruby,
    /// PHP
    Php,
    /// Erlang/Elixir
    Erlang,
    /// C/C++
    Cpp,
    /// Swift
    Swift,
    /// Kotlin/JVM
    Kotlin,
    /// Scala/JVM
    Scala,
    /// GraalVM
    Graalvm,
    /// WebAssembly
    Wasm,
    /// Other runtime
    Other,
}

impl ProcessRuntime {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            ProcessRuntime::Rust => "rust",
            ProcessRuntime::Go => "go",
            ProcessRuntime::Java => "java",
            ProcessRuntime::Nodejs => "nodejs",
            ProcessRuntime::Python => "python",
            ProcessRuntime::Dotnet => "dotnet",
            ProcessRuntime::Ruby => "ruby",
            ProcessRuntime::Php => "php",
            ProcessRuntime::Erlang => "erlang",
            ProcessRuntime::Cpp => "cpp",
            ProcessRuntime::Swift => "swift",
            ProcessRuntime::Kotlin => "kotlin",
            ProcessRuntime::Scala => "scala",
            ProcessRuntime::Graalvm => "graalvm",
            ProcessRuntime::Wasm => "wasm",
            ProcessRuntime::Other => "other",
        }
    }

    /// Returns a user-friendly name
    pub fn display_name(&self) -> &'static str {
        match self {
            ProcessRuntime::Rust => "Rust",
            ProcessRuntime::Go => "Go",
            ProcessRuntime::Java => "Java",
            ProcessRuntime::Nodejs => "Node.js",
            ProcessRuntime::Python => "Python",
            ProcessRuntime::Dotnet => ".NET",
            ProcessRuntime::Ruby => "Ruby",
            ProcessRuntime::Php => "PHP",
            ProcessRuntime::Erlang => "Erlang/OTP",
            ProcessRuntime::Cpp => "C/C++",
            ProcessRuntime::Swift => "Swift",
            ProcessRuntime::Kotlin => "Kotlin",
            ProcessRuntime::Scala => "Scala",
            ProcessRuntime::Graalvm => "GraalVM",
            ProcessRuntime::Wasm => "WebAssembly",
            ProcessRuntime::Other => "Other",
        }
    }
}

impl std::fmt::Display for ProcessRuntime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Process states
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcessState {
    /// Running
    Running,
    /// Sleeping (waiting for an event)
    Sleeping,
    /// Disk sleep (uninterruptible)
    DiskSleep,
    /// Stopped (by job control signal)
    Stopped,
    /// Tracing stop (being debugged)
    TracingStop,
    /// Zombie (defunct)
    Zombie,
    /// Dead
    Dead,
    /// Idle
    Idle,
    /// Unknown state
    Unknown,
}

impl ProcessState {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            ProcessState::Running => "running",
            ProcessState::Sleeping => "sleeping",
            ProcessState::DiskSleep => "disk_sleep",
            ProcessState::Stopped => "stopped",
            ProcessState::TracingStop => "tracing_stop",
            ProcessState::Zombie => "zombie",
            ProcessState::Dead => "dead",
            ProcessState::Idle => "idle",
            ProcessState::Unknown => "unknown",
        }
    }
}

/// Process attributes following OpenTelemetry semantic conventions
#[derive(Debug, Clone)]
pub struct ProcessAttributes {
    attributes: AttributeMap,
}

impl ProcessAttributes {
    /// Get all attributes as a map
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }

    /// Get a specific attribute
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.attributes.get(key)
    }
}

/// Builder for process attributes
#[derive(Debug, Default)]
pub struct ProcessAttributesBuilder {
    // Process identification
    pid: Option<i64>,
    parent_pid: Option<i64>,

    // Command information
    command: Option<String>,
    command_line: Option<String>,
    command_args: Vec<String>,
    executable_path: Option<String>,
    executable_name: Option<String>,

    // Process owner
    owner: Option<String>,
    owner_uid: Option<i64>,
    owner_gid: Option<i64>,

    // Process group and session
    group_pid: Option<i64>,
    session_leader_pid: Option<i64>,

    // Runtime information
    runtime: Option<ProcessRuntime>,
    runtime_version: Option<String>,
    runtime_description: Option<String>,

    // Process state
    state: Option<ProcessState>,

    // Process limits
    virtual_memory_max: Option<i64>,
    resident_memory_max: Option<i64>,
    cpu_max: Option<f64>,
    file_descriptors_max: Option<i64>,

    // Working directory
    working_directory: Option<String>,

    // Environment (select keys only, be careful with secrets)
    environment: HashMap<String, String>,

    // Custom attributes
    custom: HashMap<String, AttributeValue>,
}

impl ProcessAttributesBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self::default()
    }

    /// Set process ID (PID)
    pub fn pid(mut self, pid: i64) -> Self {
        self.pid = Some(pid);
        self
    }

    /// Set parent process ID (PPID)
    pub fn parent_pid(mut self, ppid: i64) -> Self {
        self.parent_pid = Some(ppid);
        self
    }

    /// Set command name
    pub fn command(mut self, cmd: impl Into<String>) -> Self {
        self.command = Some(cmd.into());
        self
    }

    /// Set full command line
    pub fn command_line(mut self, cmd_line: impl Into<String>) -> Self {
        self.command_line = Some(cmd_line.into());
        self
    }

    /// Add command argument
    pub fn add_command_arg(mut self, arg: impl Into<String>) -> Self {
        self.command_args.push(arg.into());
        self
    }

    /// Set command arguments
    pub fn command_args(mut self, args: Vec<String>) -> Self {
        self.command_args = args;
        self
    }

    /// Set executable path
    pub fn executable_path(mut self, path: impl Into<String>) -> Self {
        self.executable_path = Some(path.into());
        self
    }

    /// Set executable name
    pub fn executable_name(mut self, name: impl Into<String>) -> Self {
        self.executable_name = Some(name.into());
        self
    }

    /// Set process owner (username)
    pub fn owner(mut self, owner: impl Into<String>) -> Self {
        self.owner = Some(owner.into());
        self
    }

    /// Set owner UID
    pub fn owner_uid(mut self, uid: i64) -> Self {
        self.owner_uid = Some(uid);
        self
    }

    /// Set owner GID
    pub fn owner_gid(mut self, gid: i64) -> Self {
        self.owner_gid = Some(gid);
        self
    }

    /// Set process group ID (PGID)
    pub fn group_pid(mut self, pgid: i64) -> Self {
        self.group_pid = Some(pgid);
        self
    }

    /// Set session leader PID (SID)
    pub fn session_leader_pid(mut self, sid: i64) -> Self {
        self.session_leader_pid = Some(sid);
        self
    }

    /// Set runtime type
    pub fn runtime(mut self, runtime: ProcessRuntime) -> Self {
        self.runtime = Some(runtime);
        self
    }

    /// Set runtime version
    pub fn runtime_version(mut self, version: impl Into<String>) -> Self {
        self.runtime_version = Some(version.into());
        self
    }

    /// Set runtime description
    pub fn runtime_description(mut self, desc: impl Into<String>) -> Self {
        self.runtime_description = Some(desc.into());
        self
    }

    /// Set process state
    pub fn state(mut self, state: ProcessState) -> Self {
        self.state = Some(state);
        self
    }

    /// Set maximum virtual memory (bytes)
    pub fn virtual_memory_max(mut self, bytes: i64) -> Self {
        self.virtual_memory_max = Some(bytes);
        self
    }

    /// Set maximum resident memory (bytes)
    pub fn resident_memory_max(mut self, bytes: i64) -> Self {
        self.resident_memory_max = Some(bytes);
        self
    }

    /// Set maximum CPU (cores)
    pub fn cpu_max(mut self, cores: f64) -> Self {
        self.cpu_max = Some(cores);
        self
    }

    /// Set maximum file descriptors
    pub fn file_descriptors_max(mut self, max: i64) -> Self {
        self.file_descriptors_max = Some(max);
        self
    }

    /// Set working directory
    pub fn working_directory(mut self, dir: impl Into<String>) -> Self {
        self.working_directory = Some(dir.into());
        self
    }

    /// Add environment variable (use with caution - avoid secrets)
    pub fn environment_variable(
        mut self,
        key: impl Into<String>,
        value: impl Into<String>,
    ) -> Self {
        self.environment.insert(key.into(), value.into());
        self
    }

    /// Set environment variables (use with caution - avoid secrets)
    pub fn environment(mut self, env: HashMap<String, String>) -> Self {
        self.environment = env;
        self
    }

    /// Add a custom attribute
    pub fn custom_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.custom.insert(key.into(), value);
        self
    }

    /// Build the process attributes
    pub fn build(self) -> Result<ProcessAttributes> {
        let mut attributes = AttributeMap::new();

        // Process identification
        if let Some(pid) = self.pid {
            attributes.insert("process.pid".to_string(), AttributeValue::Int(pid));
        }

        if let Some(ppid) = self.parent_pid {
            attributes.insert("process.parent_pid".to_string(), AttributeValue::Int(ppid));
        }

        // Command information
        if let Some(cmd) = self.command {
            attributes.insert("process.command".to_string(), AttributeValue::String(cmd));
        }

        if let Some(cmd_line) = self.command_line {
            attributes.insert(
                "process.command_line".to_string(),
                AttributeValue::String(cmd_line),
            );
        }

        if !self.command_args.is_empty() {
            attributes.insert(
                "process.command_args".to_string(),
                AttributeValue::Array(
                    self.command_args
                        .into_iter()
                        .map(AttributeValue::String)
                        .collect(),
                ),
            );
        }

        if let Some(path) = self.executable_path {
            attributes.insert(
                "process.executable.path".to_string(),
                AttributeValue::String(path),
            );
        }

        if let Some(name) = self.executable_name {
            attributes.insert(
                "process.executable.name".to_string(),
                AttributeValue::String(name),
            );
        }

        // Owner
        if let Some(owner) = self.owner {
            attributes.insert("process.owner".to_string(), AttributeValue::String(owner));
        }

        if let Some(uid) = self.owner_uid {
            attributes.insert("process.uid".to_string(), AttributeValue::Int(uid));
        }

        if let Some(gid) = self.owner_gid {
            attributes.insert("process.gid".to_string(), AttributeValue::Int(gid));
        }

        // Process group and session
        if let Some(pgid) = self.group_pid {
            attributes.insert("process.group_pid".to_string(), AttributeValue::Int(pgid));
        }

        if let Some(sid) = self.session_leader_pid {
            attributes.insert(
                "process.session_leader_pid".to_string(),
                AttributeValue::Int(sid),
            );
        }

        // Runtime information
        if let Some(runtime) = self.runtime {
            attributes.insert(
                "process.runtime.name".to_string(),
                AttributeValue::String(runtime.display_name().to_string()),
            );
        }

        if let Some(version) = self.runtime_version {
            attributes.insert(
                "process.runtime.version".to_string(),
                AttributeValue::String(version),
            );
        }

        if let Some(desc) = self.runtime_description {
            attributes.insert(
                "process.runtime.description".to_string(),
                AttributeValue::String(desc),
            );
        }

        // Process state
        if let Some(state) = self.state {
            attributes.insert(
                "process.state".to_string(),
                AttributeValue::String(state.as_str().to_string()),
            );
        }

        // Limits
        if let Some(vmax) = self.virtual_memory_max {
            attributes.insert(
                "process.virtual_memory.max".to_string(),
                AttributeValue::Int(vmax),
            );
        }

        if let Some(rmax) = self.resident_memory_max {
            attributes.insert(
                "process.resident_memory.max".to_string(),
                AttributeValue::Int(rmax),
            );
        }

        if let Some(cpu) = self.cpu_max {
            attributes.insert("process.cpu.max".to_string(), AttributeValue::Double(cpu));
        }

        if let Some(fdmax) = self.file_descriptors_max {
            attributes.insert(
                "process.file_descriptors.max".to_string(),
                AttributeValue::Int(fdmax),
            );
        }

        // Working directory
        if let Some(dir) = self.working_directory {
            attributes.insert(
                "process.working_directory".to_string(),
                AttributeValue::String(dir),
            );
        }

        // Environment (select keys only)
        for (key, value) in self.environment {
            attributes.insert(
                format!("process.environment.{}", key),
                AttributeValue::String(value),
            );
        }

        // Add custom attributes
        attributes.extend(self.custom);

        Ok(ProcessAttributes { attributes })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_runtime() {
        assert_eq!(ProcessRuntime::Rust.as_str(), "rust");
        assert_eq!(ProcessRuntime::Go.as_str(), "go");
        assert_eq!(ProcessRuntime::Java.as_str(), "java");
        assert_eq!(ProcessRuntime::Nodejs.as_str(), "nodejs");
        assert_eq!(ProcessRuntime::Python.as_str(), "python");
    }

    #[test]
    fn test_process_runtime_display_name() {
        assert_eq!(ProcessRuntime::Rust.display_name(), "Rust");
        assert_eq!(ProcessRuntime::Nodejs.display_name(), "Node.js");
        assert_eq!(ProcessRuntime::Dotnet.display_name(), ".NET");
    }

    #[test]
    fn test_process_state() {
        assert_eq!(ProcessState::Running.as_str(), "running");
        assert_eq!(ProcessState::Sleeping.as_str(), "sleeping");
        assert_eq!(ProcessState::Zombie.as_str(), "zombie");
    }

    #[test]
    fn test_process_attributes_builder_minimal() {
        let attrs = ProcessAttributesBuilder::new().build().unwrap();
        assert!(attrs.as_map().is_empty());
    }

    #[test]
    fn test_process_attributes_builder_full() {
        let attrs = ProcessAttributesBuilder::new()
            .pid(1234)
            .parent_pid(1)
            .command("my-app")
            .command_line("my-app --port 8080")
            .add_command_arg("--port")
            .add_command_arg("8080")
            .executable_path("/usr/bin/my-app")
            .executable_name("my-app")
            .owner("appuser")
            .owner_uid(1000)
            .owner_gid(1000)
            .runtime(ProcessRuntime::Rust)
            .runtime_version("1.75.0")
            .state(ProcessState::Running)
            .working_directory("/app")
            .build()
            .unwrap();

        assert_eq!(attrs.get("process.pid"), Some(&AttributeValue::Int(1234)));
        assert_eq!(
            attrs.get("process.parent_pid"),
            Some(&AttributeValue::Int(1))
        );
        assert_eq!(
            attrs.get("process.command"),
            Some(&AttributeValue::String("my-app".to_string()))
        );
        assert_eq!(
            attrs.get("process.executable.path"),
            Some(&AttributeValue::String("/usr/bin/my-app".to_string()))
        );
        assert_eq!(
            attrs.get("process.runtime.name"),
            Some(&AttributeValue::String("Rust".to_string()))
        );
        assert_eq!(
            attrs.get("process.runtime.version"),
            Some(&AttributeValue::String("1.75.0".to_string()))
        );
        assert_eq!(
            attrs.get("process.state"),
            Some(&AttributeValue::String("running".to_string()))
        );
    }

    #[test]
    fn test_process_limits() {
        let attrs = ProcessAttributesBuilder::new()
            .pid(1234)
            .virtual_memory_max(1073741824)
            .resident_memory_max(536870912)
            .cpu_max(2.0)
            .file_descriptors_max(65536)
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("process.virtual_memory.max"),
            Some(&AttributeValue::Int(1073741824))
        );
        assert_eq!(
            attrs.get("process.resident_memory.max"),
            Some(&AttributeValue::Int(536870912))
        );
        assert_eq!(
            attrs.get("process.cpu.max"),
            Some(&AttributeValue::Double(2.0))
        );
        assert_eq!(
            attrs.get("process.file_descriptors.max"),
            Some(&AttributeValue::Int(65536))
        );
    }

    #[test]
    fn test_process_environment() {
        let attrs = ProcessAttributesBuilder::new()
            .pid(1234)
            .environment_variable("APP_ENV", "production")
            .environment_variable("APP_PORT", "8080")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("process.environment.APP_ENV"),
            Some(&AttributeValue::String("production".to_string()))
        );
        assert_eq!(
            attrs.get("process.environment.APP_PORT"),
            Some(&AttributeValue::String("8080".to_string()))
        );
    }

    #[test]
    fn test_process_command_args() {
        let args = vec![
            "my-app".to_string(),
            "--config".to_string(),
            "/etc/app.conf".to_string(),
            "--verbose".to_string(),
        ];

        let attrs = ProcessAttributesBuilder::new()
            .pid(1234)
            .command_args(args)
            .build()
            .unwrap();

        let cmd_args = attrs.get("process.command_args");
        assert!(cmd_args.is_some());
        if let Some(AttributeValue::Array(arr)) = cmd_args {
            assert_eq!(arr.len(), 4);
            assert_eq!(arr[0], AttributeValue::String("my-app".to_string()));
        }
    }

    #[test]
    fn test_process_session_group() {
        let attrs = ProcessAttributesBuilder::new()
            .pid(1234)
            .group_pid(1234)
            .session_leader_pid(1234)
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("process.group_pid"),
            Some(&AttributeValue::Int(1234))
        );
        assert_eq!(
            attrs.get("process.session_leader_pid"),
            Some(&AttributeValue::Int(1234))
        );
    }

    #[test]
    fn test_process_custom_attributes() {
        let attrs = ProcessAttributesBuilder::new()
            .pid(1234)
            .custom_attribute("custom.thread_count", AttributeValue::Int(16))
            .custom_attribute("custom.open_files", AttributeValue::Int(42))
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("custom.thread_count"),
            Some(&AttributeValue::Int(16))
        );
        assert_eq!(
            attrs.get("custom.open_files"),
            Some(&AttributeValue::Int(42))
        );
    }

    #[test]
    fn test_all_runtimes() {
        let runtimes = vec![
            ProcessRuntime::Rust,
            ProcessRuntime::Go,
            ProcessRuntime::Java,
            ProcessRuntime::Nodejs,
            ProcessRuntime::Python,
            ProcessRuntime::Dotnet,
            ProcessRuntime::Ruby,
            ProcessRuntime::Php,
        ];

        for runtime in runtimes {
            let attrs = ProcessAttributesBuilder::new()
                .pid(1)
                .runtime(runtime)
                .build()
                .unwrap();

            assert!(
                attrs.get("process.runtime.name").is_some(),
                "runtime.name should be present for {:?}",
                runtime
            );
        }
    }
}
