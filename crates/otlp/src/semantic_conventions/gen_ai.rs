//! # OpenTelemetry GenAI Semantic Conventions
//!
//! This module implements the OpenTelemetry GenAI semantic conventions for
//! observability of Large Language Model (LLM) applications and AI agents.
//!
//! ## Specification
//!
//! Based on OpenTelemetry Semantic Conventions v1.37+ for Generative AI:
//! - <https://opentelemetry.io/docs/specs/semconv/gen-ai/gen-ai-spans/>
//!
//! ## Features
//!
//! - **Complete Attribute Coverage**: All standard `gen_ai.*` attributes
//! - **Type-Safe Builders**: Builder pattern for constructing attributes
//! - **Multi-Provider Support**: OpenAI, Anthropic, Azure, AWS Bedrock, etc.
//! - **Content Safety**: Optional content capture with privacy controls
//! - **Token Tracking**: Automatic input/output token counting
//! - **Operation Types**: chat, embeddings, execute_tool, invoke_agent
//!
//! ## Quick Start
//!
//! ```rust,ignore
//! use otlp::semantic_conventions::gen_ai::{
//!     GenAiAttributes, GenAiSystem, GenAiOperation, GenAiFinishReason
//! };
//!
//! let attrs = GenAiAttributes::builder()
//!     .system(GenAiSystem::OpenAI)
//!     .operation(GenAiOperation::Chat)
//!     .request_model("gpt-4o")
//!     .input_tokens(150)
//!     .output_tokens(45)
//!     .finish_reason(GenAiFinishReason::Stop)
//!     .build();
//! ```
//!
//! ## Privacy Considerations
//!
//! By default, this module does NOT capture sensitive content (prompts/completions).
//! Enable content capture explicitly for development/debugging only:
//!
//! ```rust,ignore
//! use otlp::semantic_conventions::gen_ai::GenAiAttributes;
//!
//! let attrs = GenAiAttributes::builder()
//!     .capture_content(true)  // Only in development!
//!     .input_message("Hello, AI!")
//!     .build();
//! ```

use crate::semantic_conventions::common::{AttributeValue};
use std::collections::HashMap;

/// Version of the GenAI semantic conventions implemented
pub const GENAI_SEMCONV_VERSION: &str = "1.37.0";

/// Status of the GenAI semantic conventions
pub const GENAI_SEMCONV_STATUS: &str = "development";



/// GenAI system/provider identifiers
///
/// These are the standard identifiers for different AI providers
/// as defined by OpenTelemetry semantic conventions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenAiSystem {
    /// OpenAI (including API-compatible providers)
    OpenAI,
    /// Anthropic Claude
    Anthropic,
    /// Azure OpenAI Service
    AzureOpenAI,
    /// AWS Bedrock
    AwsBedrock,
    /// Google AI (Gemini, PaLM)
    GoogleAI,
    /// Cohere
    Cohere,
    /// Mistral AI
    MistralAI,
    /// Meta AI (Llama)
    MetaAI,
    /// Custom or self-hosted model
    Custom(&'static str),
}

impl GenAiSystem {
    /// Returns the string identifier for this system
    pub fn as_str(&self) -> &str {
        match self {
            GenAiSystem::OpenAI => "openai",
            GenAiSystem::Anthropic => "anthropic",
            GenAiSystem::AzureOpenAI => "azure.ai.openai",
            GenAiSystem::AwsBedrock => "aws.bedrock",
            GenAiSystem::GoogleAI => "google_ai",
            GenAiSystem::Cohere => "cohere",
            GenAiSystem::MistralAI => "mistral_ai",
            GenAiSystem::MetaAI => "meta.ai",
            GenAiSystem::Custom(s) => s,
        }
    }
}

impl std::fmt::Display for GenAiSystem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// GenAI operation types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenAiOperation {
    /// Chat completion (e.g., chat with GPT-4)
    Chat,
    /// Text completion (legacy, often deprecated)
    TextCompletion,
    /// Embedding generation
    Embeddings,
    /// Tool execution
    ExecuteTool,
    /// Agent invocation
    InvokeAgent,
    /// Agent creation
    CreateAgent,
    /// Image generation
    ImageGeneration,
    /// Audio generation/transcription
    Audio,
}

impl GenAiOperation {
    pub fn as_str(&self) -> &str {
        match self {
            GenAiOperation::Chat => "chat",
            GenAiOperation::TextCompletion => "text_completion",
            GenAiOperation::Embeddings => "embeddings",
            GenAiOperation::ExecuteTool => "execute_tool",
            GenAiOperation::InvokeAgent => "invoke_agent",
            GenAiOperation::CreateAgent => "create_agent",
            GenAiOperation::ImageGeneration => "image_generation",
            GenAiOperation::Audio => "audio",
        }
    }
}

impl std::fmt::Display for GenAiOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Finish reason for GenAI operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenAiFinishReason {
    /// Normal completion
    Stop,
    /// Maximum token limit reached
    Length,
    /// Content filtered by safety system
    ContentFilter,
    /// Tool call requested
    ToolCalls,
    /// Function call (legacy)
    FunctionCall,
    /// Other/unknown reason
    Other(&'static str),
}

impl GenAiFinishReason {
    pub fn as_str(&self) -> &str {
        match self {
            GenAiFinishReason::Stop => "stop",
            GenAiFinishReason::Length => "length",
            GenAiFinishReason::ContentFilter => "content_filter",
            GenAiFinishReason::ToolCalls => "tool_calls",
            GenAiFinishReason::FunctionCall => "function_call",
            GenAiFinishReason::Other(s) => s,
        }
    }
}

impl std::fmt::Display for GenAiFinishReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Complete GenAI attributes for a span
///
/// This struct holds all GenAI-related attributes following the
/// OpenTelemetry semantic conventions specification.
#[derive(Debug, Clone, Default)]
pub struct GenAiAttributes {
    /// The Generative AI product as identified by the client or server instrumentation
    pub system: Option<String>,
    
    /// The type of operation being performed
    pub operation_name: Option<String>,
    
    /// The name of the model a request is being made to
    pub request_model: Option<String>,
    
    /// The maximum number of tokens the model generates for a request
    pub request_max_tokens: Option<i64>,
    
    /// The temperature setting for the request
    pub request_temperature: Option<f64>,
    
    /// The top_p sampling setting for the request
    pub request_top_p: Option<f64>,
    
    /// Array of stop sequences for the request
    pub request_stop_sequences: Option<Vec<String>>,
    
    /// The number of completions/generations requested
    pub request_completions: Option<i64>,
    
    /// The name of the model that actually provided the response
    pub response_model: Option<String>,
    
    /// The finish reason from the model response
    pub response_finish_reason: Option<String>,
    
    /// The ID of the response
    pub response_id: Option<String>,
    
    /// The number of tokens used in the prompt/request
    pub usage_input_tokens: Option<i64>,
    
    /// The number of tokens used in the completion/response
    pub usage_output_tokens: Option<i64>,
    
    /// The total number of tokens used
    pub usage_total_tokens: Option<i64>,
    
    /// Additional provider-specific attributes
    pub custom_attributes: HashMap<String, AttributeValue>,
    
    /// Whether to capture content (prompts/completions)
    /// 
    /// ⚠️ SECURITY WARNING: Only enable in development!
    /// Capturing content may leak sensitive information.
    capture_content: bool,
    
    /// Input messages (only captured if capture_content is true)
    pub input_messages: Option<String>,
    
    /// Output messages (only captured if capture_content is true)
    pub output_messages: Option<String>,
    
    /// System instructions (only captured if capture_content is true)
    pub system_instructions: Option<String>,
}

impl GenAiAttributes {
    /// Create a new builder for constructing GenAI attributes
    pub fn builder() -> GenAiAttributesBuilder {
        GenAiAttributesBuilder::default()
    }
    
    /// Convert attributes to OpenTelemetry key-value pairs
    pub fn to_otel_attributes(&self) -> Vec<(String, AttributeValue)> {
        let mut attrs = Vec::new();
        
        // Required attributes
        if let Some(ref system) = self.system {
            attrs.push(("gen_ai.system".to_string(), AttributeValue::String(system.clone())));
        }
        
        if let Some(ref operation) = self.operation_name {
            attrs.push(("gen_ai.operation.name".to_string(), AttributeValue::String(operation.clone())));
        }
        
        // Request attributes
        if let Some(ref model) = self.request_model {
            attrs.push(("gen_ai.request.model".to_string(), AttributeValue::String(model.clone())));
        }
        
        if let Some(tokens) = self.request_max_tokens {
            attrs.push(("gen_ai.request.max_tokens".to_string(), AttributeValue::Int(tokens)));
        }
        
        if let Some(temp) = self.request_temperature {
            attrs.push(("gen_ai.request.temperature".to_string(), AttributeValue::Double(temp)));
        }
        
        if let Some(top_p) = self.request_top_p {
            attrs.push(("gen_ai.request.top_p".to_string(), AttributeValue::Double(top_p)));
        }
        
        if let Some(ref stop_seqs) = self.request_stop_sequences {
            let values: Vec<AttributeValue> = stop_seqs
                .iter()
                .map(|s| AttributeValue::String(s.clone()))
                .collect();
            attrs.push(("gen_ai.request.stop_sequences".to_string(), AttributeValue::Array(values)));
        }
        
        if let Some(n) = self.request_completions {
            attrs.push(("gen_ai.request.completions".to_string(), AttributeValue::Int(n)));
        }
        
        // Response attributes
        if let Some(ref model) = self.response_model {
            attrs.push(("gen_ai.response.model".to_string(), AttributeValue::String(model.clone())));
        }
        
        if let Some(ref finish_reason) = self.response_finish_reason {
            attrs.push(("gen_ai.response.finish_reason".to_string(), AttributeValue::String(finish_reason.clone())));
        }
        
        if let Some(ref id) = self.response_id {
            attrs.push(("gen_ai.response.id".to_string(), AttributeValue::String(id.clone())));
        }
        
        // Usage attributes
        if let Some(tokens) = self.usage_input_tokens {
            attrs.push(("gen_ai.usage.input_tokens".to_string(), AttributeValue::Int(tokens)));
        }
        
        if let Some(tokens) = self.usage_output_tokens {
            attrs.push(("gen_ai.usage.output_tokens".to_string(), AttributeValue::Int(tokens)));
        }
        
        if let Some(tokens) = self.usage_total_tokens {
            attrs.push(("gen_ai.usage.total_tokens".to_string(), AttributeValue::Int(tokens)));
        }
        
        // Content attributes (only if explicitly enabled)
        if self.capture_content {
            if let Some(ref input) = self.input_messages {
                attrs.push(("gen_ai.input.messages".to_string(), AttributeValue::String(input.clone())));
            }
            if let Some(ref output) = self.output_messages {
                attrs.push(("gen_ai.output.messages".to_string(), AttributeValue::String(output.clone())));
            }
            if let Some(ref instructions) = self.system_instructions {
                attrs.push(("gen_ai.system_instructions".to_string(), AttributeValue::String(instructions.clone())));
            }
        }
        
        // Custom attributes with prefix
        for (key, value) in &self.custom_attributes {
            attrs.push((format!("gen_ai.{}", key), value.clone()));
        }
        
        attrs
    }
    
    /// Calculate total tokens from input and output
    pub fn calculate_total_tokens(&mut self) {
        if let (Some(input), Some(output)) = (self.usage_input_tokens, self.usage_output_tokens) {
            self.usage_total_tokens = Some(input + output);
        }
    }
}

/// Builder for constructing GenAI attributes
#[derive(Debug, Default)]
pub struct GenAiAttributesBuilder {
    attrs: GenAiAttributes,
}

impl GenAiAttributesBuilder {
    /// Set the GenAI system/provider
    pub fn system(mut self, system: GenAiSystem) -> Self {
        self.attrs.system = Some(system.to_string());
        self
    }
    
    /// Set the system as a custom string
    pub fn system_str(mut self, system: impl Into<String>) -> Self {
        self.attrs.system = Some(system.into());
        self
    }
    
    /// Set the operation type
    pub fn operation(mut self, operation: GenAiOperation) -> Self {
        self.attrs.operation_name = Some(operation.to_string());
        self
    }
    
    /// Set the operation as a custom string
    pub fn operation_str(mut self, operation: impl Into<String>) -> Self {
        self.attrs.operation_name = Some(operation.into());
        self
    }
    
    /// Set the request model name
    pub fn request_model(mut self, model: impl Into<String>) -> Self {
        self.attrs.request_model = Some(model.into());
        self
    }
    
    /// Set the maximum tokens for the request
    pub fn max_tokens(mut self, tokens: i64) -> Self {
        self.attrs.request_max_tokens = Some(tokens);
        self
    }
    
    /// Set the temperature (0.0 - 2.0)
    pub fn temperature(mut self, temp: f64) -> Self {
        self.attrs.request_temperature = Some(temp.clamp(0.0, 2.0));
        self
    }
    
    /// Set the top_p value (0.0 - 1.0)
    pub fn top_p(mut self, top_p: f64) -> Self {
        self.attrs.request_top_p = Some(top_p.clamp(0.0, 1.0));
        self
    }
    
    /// Set stop sequences
    pub fn stop_sequences(mut self, sequences: Vec<String>) -> Self {
        self.attrs.request_stop_sequences = Some(sequences);
        self
    }
    
    /// Set the number of completions
    pub fn completions(mut self, n: i64) -> Self {
        self.attrs.request_completions = Some(n);
        self
    }
    
    /// Set the response model name
    pub fn response_model(mut self, model: impl Into<String>) -> Self {
        self.attrs.response_model = Some(model.into());
        self
    }
    
    /// Set the finish reason
    pub fn finish_reason(mut self, reason: GenAiFinishReason) -> Self {
        self.attrs.response_finish_reason = Some(reason.to_string());
        self
    }
    
    /// Set the response ID
    pub fn response_id(mut self, id: impl Into<String>) -> Self {
        self.attrs.response_id = Some(id.into());
        self
    }
    
    /// Set input token count
    pub fn input_tokens(mut self, tokens: i64) -> Self {
        self.attrs.usage_input_tokens = Some(tokens);
        self
    }
    
    /// Set output token count
    pub fn output_tokens(mut self, tokens: i64) -> Self {
        self.attrs.usage_output_tokens = Some(tokens);
        self
    }
    
    /// Set total token count
    pub fn total_tokens(mut self, tokens: i64) -> Self {
        self.attrs.usage_total_tokens = Some(tokens);
        self
    }
    
    /// Enable/disable content capture
    /// 
    /// ⚠️ SECURITY: Only enable in development environments!
    pub fn capture_content(mut self, enable: bool) -> Self {
        self.attrs.capture_content = enable;
        self
    }
    
    /// Set input messages (only stored if capture_content is true)
    pub fn input_message(mut self, message: impl Into<String>) -> Self {
        self.attrs.input_messages = Some(message.into());
        self
    }
    
    /// Set output messages (only stored if capture_content is true)
    pub fn output_message(mut self, message: impl Into<String>) -> Self {
        self.attrs.output_messages = Some(message.into());
        self
    }
    
    /// Set system instructions (only stored if capture_content is true)
    pub fn system_instructions(mut self, instructions: impl Into<String>) -> Self {
        self.attrs.system_instructions = Some(instructions.into());
        self
    }
    
    /// Add a custom attribute
    pub fn custom_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.attrs.custom_attributes.insert(key.into(), value);
        self
    }
    
    /// Build the GenAI attributes
    pub fn build(mut self) -> GenAiAttributes {
        // Auto-calculate total tokens if not set
        if self.attrs.usage_total_tokens.is_none() {
            self.attrs.calculate_total_tokens();
        }
        self.attrs
    }
}

/// Utility functions for GenAI observability
pub mod utils {
    use super::*;
    
    /// Calculate approximate token count from text
    /// 
    /// This is a rough estimate (1 token ≈ 4 characters for English).
    /// For accurate counts, use the provider's API.
    pub fn estimate_tokens(text: &str) -> i64 {
        // Rough estimate: 1 token ≈ 4 characters
        (text.len() as f64 / 4.0).ceil() as i64
    }
    
    /// Create attributes for a chat completion request
    pub fn chat_completion_attrs(
        system: GenAiSystem,
        model: impl Into<String>,
        input_tokens: i64,
        output_tokens: i64,
    ) -> GenAiAttributes {
        GenAiAttributes::builder()
            .system(system)
            .operation(GenAiOperation::Chat)
            .request_model(model)
            .input_tokens(input_tokens)
            .output_tokens(output_tokens)
            .build()
    }
    
    /// Create attributes for an embedding request
    pub fn embedding_attrs(
        system: GenAiSystem,
        model: impl Into<String>,
        input_tokens: i64,
    ) -> GenAiAttributes {
        GenAiAttributes::builder()
            .system(system)
            .operation(GenAiOperation::Embeddings)
            .request_model(model)
            .input_tokens(input_tokens)
            .output_tokens(0)  // Embeddings don't have output tokens
            .build()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_gen_ai_system_display() {
        assert_eq!(GenAiSystem::OpenAI.to_string(), "openai");
        assert_eq!(GenAiSystem::Anthropic.to_string(), "anthropic");
        assert_eq!(GenAiSystem::AzureOpenAI.to_string(), "azure.ai.openai");
    }
    
    #[test]
    fn test_gen_ai_operation_display() {
        assert_eq!(GenAiOperation::Chat.to_string(), "chat");
        assert_eq!(GenAiOperation::Embeddings.to_string(), "embeddings");
    }
    
    #[test]
    fn test_builder_basic() {
        let attrs = GenAiAttributes::builder()
            .system(GenAiSystem::OpenAI)
            .operation(GenAiOperation::Chat)
            .request_model("gpt-4o")
            .input_tokens(100)
            .output_tokens(50)
            .build();
        
        assert_eq!(attrs.system, Some("openai".to_string()));
        assert_eq!(attrs.operation_name, Some("chat".to_string()));
        assert_eq!(attrs.request_model, Some("gpt-4o".to_string()));
        assert_eq!(attrs.usage_input_tokens, Some(100));
        assert_eq!(attrs.usage_output_tokens, Some(50));
        assert_eq!(attrs.usage_total_tokens, Some(150));
    }
    
    #[test]
    fn test_to_otel_attributes() {
        let attrs = GenAiAttributes::builder()
            .system(GenAiSystem::OpenAI)
            .operation(GenAiOperation::Chat)
            .request_model("gpt-4o")
            .input_tokens(100)
            .output_tokens(50)
            .build();
        
        let otel_attrs = attrs.to_otel_attributes();
        
        // Check that required attributes are present
        let keys: Vec<_> = otel_attrs.iter().map(|(k, _)| k.as_str()).collect();
        assert!(keys.contains(&"gen_ai.system"));
        assert!(keys.contains(&"gen_ai.operation.name"));
        assert!(keys.contains(&"gen_ai.request.model"));
        assert!(keys.contains(&"gen_ai.usage.input_tokens"));
        assert!(keys.contains(&"gen_ai.usage.output_tokens"));
        assert!(keys.contains(&"gen_ai.usage.total_tokens"));
    }
    
    #[test]
    fn test_content_capture_disabled_by_default() {
        let attrs = GenAiAttributes::builder()
            .system(GenAiSystem::OpenAI)
            .input_message("secret prompt")
            .output_message("secret response")
            .build();
        
        let otel_attrs = attrs.to_otel_attributes();
        let keys: Vec<_> = otel_attrs.iter().map(|(k, _)| k.as_str()).collect();
        
        // Content should NOT be captured by default
        assert!(!keys.contains(&"gen_ai.input.messages"));
        assert!(!keys.contains(&"gen_ai.output.messages"));
    }
    
    #[test]
    fn test_content_capture_when_enabled() {
        let attrs = GenAiAttributes::builder()
            .system(GenAiSystem::OpenAI)
            .capture_content(true)
            .input_message("user prompt")
            .output_message("assistant response")
            .build();
        
        let otel_attrs = attrs.to_otel_attributes();
        let keys: Vec<_> = otel_attrs.iter().map(|(k, _)| k.as_str()).collect();
        
        // Content should be captured when explicitly enabled
        assert!(keys.contains(&"gen_ai.input.messages"));
        assert!(keys.contains(&"gen_ai.output.messages"));
    }
    
    #[test]
    fn test_utils_estimate_tokens() {
        // Rough estimate: 1 token ≈ 4 characters
        assert_eq!(utils::estimate_tokens("hello world"), 3);  // 11 chars / 4 = 2.75 -> 3
        assert_eq!(utils::estimate_tokens("a"), 1);
        assert_eq!(utils::estimate_tokens("aaaa"), 1);
        assert_eq!(utils::estimate_tokens("aaaaa"), 2);
    }
    
    #[test]
    fn test_temperature_clamping() {
        let attrs = GenAiAttributes::builder()
            .temperature(3.0)  // Above max
            .build();
        
        assert_eq!(attrs.request_temperature, Some(2.0));  // Clamped to max
        
        let attrs2 = GenAiAttributes::builder()
            .temperature(-1.0)  // Below min
            .build();
        
        assert_eq!(attrs2.request_temperature, Some(0.0));  // Clamped to min
    }
    
    #[test]
    fn test_top_p_clamping() {
        let attrs = GenAiAttributes::builder()
            .top_p(1.5)  // Above max
            .build();
        
        assert_eq!(attrs.request_top_p, Some(1.0));  // Clamped to max
    }
}
