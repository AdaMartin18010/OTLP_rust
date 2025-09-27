//! # Mock服务器
//!
//! 提供测试用的Mock OTLP服务器。

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::sync::RwLock;
use warp::Filter;

/// Mock OTLP服务器
pub struct MockOtlpServer {
    pub address: SocketAddr,
    pub received_data: Arc<RwLock<Vec<serde_json::Value>>>,
    pub request_count: Arc<RwLock<u64>>,
}

impl MockOtlpServer {
    /// 创建新的Mock服务器
    pub async fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let received_data = Arc::new(RwLock::new(Vec::new()));
        let request_count = Arc::new(RwLock::new(0));
        
        let data_arc = received_data.clone();
        let count_arc = request_count.clone();
        let data_arc2 = received_data.clone();
        let count_arc2 = request_count.clone();
        let rd_ret = received_data.clone();
        let rc_ret = request_count.clone();
        let logs_data_arc = rd_ret.clone();
        let logs_count_arc = rc_ret.clone();

        // 创建路由
        let routes = warp::path("v1")
            .and(warp::path("traces"))
            .and(warp::post())
            .and(warp::body::json())
            .map(move |data: serde_json::Value| {
                let data_clone = data_arc.clone();
                let count_clone = count_arc.clone();
                
                tokio::spawn(async move {
                    let mut received = data_clone.write().await;
                    received.push(data);
                    
                    let mut count = count_clone.write().await;
                    *count += 1;
                });
                
                warp::reply::json(&serde_json::json!({
                    "status": "success"
                }))
            })
            .or(warp::path("v1")
                .and(warp::path("metrics"))
                .and(warp::post())
                .and(warp::body::json())
                .map(move |data: serde_json::Value| {
                    let data_clone = data_arc2.clone();
                    let count_clone = count_arc2.clone();
                    
                    tokio::spawn(async move {
                        let mut received = data_clone.write().await;
                        received.push(data);
                        
                        let mut count = count_clone.write().await;
                        *count += 1;
                    });
                    
                    warp::reply::json(&serde_json::json!({
                        "status": "success"
                    }))
                }))
            .or(warp::path("v1")
                .and(warp::path("logs"))
                .and(warp::post())
                .and(warp::body::json())
                .map(move |data: serde_json::Value| {
                    let data_clone = logs_data_arc.clone();
                    let count_clone = logs_count_arc.clone();
                    
                    tokio::spawn(async move {
                        let mut received = data_clone.write().await;
                        received.push(data);
                        
                        let mut count = count_clone.write().await;
                        *count += 1;
                    });
                    
                    warp::reply::json(&serde_json::json!({
                        "status": "success"
                    }))
                }));

        // 使用一个固定的端口来避免复杂的动态端口分配
        let port = 30000 + (std::process::id() % 1000) as u16; // 基于进程ID选择端口
        let address = std::net::SocketAddr::from(([127, 0, 0, 1], port));
        
        // 启动服务器
        let server = warp::serve(routes);
        
        // 在后台运行服务器
        let server_future = server.run(address);
        tokio::spawn(server_future);
        
        // 等待服务器启动
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        Ok(Self {
            address,
            received_data: rd_ret,
            request_count: rc_ret,
        })
    }
    
    /// 获取接收到的数据
    pub async fn get_received_data(&self) -> Vec<serde_json::Value> {
        self.received_data.read().await.clone()
    }
    
    /// 获取请求计数
    pub async fn get_request_count(&self) -> u64 {
        *self.request_count.read().await
    }
    
    /// 清空接收到的数据
    pub async fn clear_received_data(&self) {
        let mut data = self.received_data.write().await;
        data.clear();
        
        let mut count = self.request_count.write().await;
        *count = 0;
    }
    
    /// 获取服务器URL
    pub fn get_url(&self) -> String {
        format!("http://{}", self.address)
    }
}

/// Mock服务器管理器
pub struct MockServerManager {
    servers: HashMap<String, MockOtlpServer>,
}

impl MockServerManager {
    /// 创建新的管理器
    pub fn new() -> Self {
        Self {
            servers: HashMap::new(),
        }
    }
    
    /// 启动Mock服务器
    pub async fn start_server(&mut self, name: &str) -> Result<(), Box<dyn std::error::Error>> {
        let server = MockOtlpServer::new().await?;
        self.servers.insert(name.to_string(), server);
        Ok(())
    }
    
    /// 获取服务器
    pub fn get_server(&self, name: &str) -> Option<&MockOtlpServer> {
        self.servers.get(name)
    }
    
    /// 停止所有服务器
    pub fn stop_all(&mut self) {
        self.servers.clear();
    }
}

impl Default for MockServerManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_mock_server_creation() {
        let server = MockOtlpServer::new().await;
        assert!(server.is_ok());
        
        let server = server.unwrap();
        assert_eq!(server.get_request_count().await, 0);
        assert!(server.get_received_data().await.is_empty());
    }

    #[tokio::test]
    async fn test_mock_server_manager() {
        let mut manager = MockServerManager::new();
        
        let result = manager.start_server("test").await;
        assert!(result.is_ok());
        
        let server = manager.get_server("test");
        assert!(server.is_some());
        
        manager.stop_all();
        assert!(manager.get_server("test").is_none());
    }
}
