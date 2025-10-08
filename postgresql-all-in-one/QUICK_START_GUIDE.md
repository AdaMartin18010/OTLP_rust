# PostgreSQL All-in-One 快速开始指南

> 🚀 **5分钟快速上手**：从零到部署完成的完整指南

## 📋 目录

- [PostgreSQL All-in-One 快速开始指南](#postgresql-all-in-one-快速开始指南)
  - [📋 目录](#-目录)
  - [🎯 环境准备](#-环境准备)
    - [最低要求](#最低要求)
    - [必备软件](#必备软件)
      - [1. Docker 安装](#1-docker-安装)
      - [2. Kubernetes 集群](#2-kubernetes-集群)
      - [3. kubectl 安装](#3-kubectl-安装)
      - [4. Helm 安装](#4-helm-安装)
  - [🚀 一键部署](#-一键部署)
    - [步骤1: 克隆项目](#步骤1-克隆项目)
    - [步骤2: 执行部署脚本](#步骤2-执行部署脚本)
    - [步骤3: 设置端口转发（可选）](#步骤3-设置端口转发可选)
  - [✅ 验证部署](#-验证部署)
    - [1. 检查Pod状态](#1-检查pod状态)
    - [2. 运行健康检查](#2-运行健康检查)
    - [3. 测试数据库连接](#3-测试数据库连接)
    - [4. 访问监控面板](#4-访问监控面板)
  - [📖 基本使用](#-基本使用)
    - [1. 创建数据库表](#1-创建数据库表)
    - [2. 插入测试数据](#2-插入测试数据)
    - [3. 使用Redis缓存](#3-使用redis缓存)
    - [4. 查看监控指标](#4-查看监控指标)
  - [🔧 常见问题](#-常见问题)
    - [问题1: Pod启动失败](#问题1-pod启动失败)
    - [问题2: 无法连接到服务](#问题2-无法连接到服务)
    - [问题3: 存储空间不足](#问题3-存储空间不足)
    - [问题4: 性能较慢](#问题4-性能较慢)
    - [问题5: 卸载后重新部署失败](#问题5-卸载后重新部署失败)
  - [🔄 日常运维](#-日常运维)
    - [备份数据](#备份数据)
    - [恢复数据](#恢复数据)
    - [性能监控](#性能监控)
    - [健康检查](#健康检查)
  - [🎓 下一步](#-下一步)
    - [学习资源](#学习资源)
    - [实践项目](#实践项目)
    - [生产环境部署](#生产环境部署)
  - [📞 获取帮助](#-获取帮助)
    - [文档](#文档)
    - [社区](#社区)
    - [贡献](#贡献)
  - [🎉 恭喜](#-恭喜)

---

## 🎯 环境准备

### 最低要求

```text
✓ CPU: 4核 2.0GHz
✓ 内存: 8GB RAM
✓ 存储: 100GB SSD
✓ 网络: 1Gbps
✓ OS: Linux/macOS/Windows
```

### 必备软件

#### 1. Docker 安装

**Linux:**

```bash
curl -fsSL https://get.docker.com -o get-docker.sh
sudo sh get-docker.sh
sudo usermod -aG docker $USER
```

**macOS:**

```bash
brew install --cask docker
```

**Windows:**
下载并安装 [Docker Desktop](https://www.docker.com/products/docker-desktop)

#### 2. Kubernetes 集群

**选项A: 本地开发（推荐初学者）**:

使用 Minikube:

```bash
# macOS
brew install minikube
minikube start --memory=8192 --cpus=4

# Linux
curl -LO https://storage.googleapis.com/minikube/releases/latest/minikube-linux-amd64
sudo install minikube-linux-amd64 /usr/local/bin/minikube
minikube start --memory=8192 --cpus=4

# Windows (PowerShell as Administrator)
choco install minikube
minikube start --memory=8192 --cpus=4
```

**选项B: Kind（轻量级）**:

```bash
# 安装Kind
GO111MODULE="on" go install sigs.k8s.io/kind@latest

# 创建集群
kind create cluster --name postgresql-all-in-one
```

**选项C: 云服务（生产环境）**:

- AWS EKS
- Google GKE
- Azure AKS
- DigitalOcean Kubernetes

#### 3. kubectl 安装

```bash
# macOS
brew install kubectl

# Linux
curl -LO "https://dl.k8s.io/release/$(curl -L -s https://dl.k8s.io/release/stable.txt)/bin/linux/amd64/kubectl"
sudo install -o root -g root -m 0755 kubectl /usr/local/bin/kubectl

# Windows (PowerShell)
choco install kubernetes-cli
```

验证安装:

```bash
kubectl version --client
kubectl cluster-info
```

#### 4. Helm 安装

```bash
# macOS
brew install helm

# Linux
curl https://raw.githubusercontent.com/helm/helm/main/scripts/get-helm-3 | bash

# Windows
choco install kubernetes-helm
```

验证安装:

```bash
helm version
```

---

## 🚀 一键部署

### 步骤1: 克隆项目

```bash
git clone <repository-url>
cd OTLP_rust/postgresql-all-in-one
```

### 步骤2: 执行部署脚本

```bash
cd scripts
chmod +x deploy.sh
./deploy.sh
```

**预期输出：**

```text
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║     PostgreSQL All-in-One 部署工具                          ║
║     为中小型团队打造的经济高效数据处理平台                   ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝

[INFO] 检查部署环境...
[SUCCESS] Docker 已安装 (版本: 24.0.0)
[SUCCESS] kubectl 已安装 (版本: v1.28.0)
[SUCCESS] Helm 已安装 (版本: v3.12.0)
[SUCCESS] Kubernetes 集群连接正常 (版本: v1.28.0)
[SUCCESS] 环境检查通过 ✓

[INFO] 创建命名空间...
[SUCCESS] 命名空间创建完成

[INFO] 部署 PostgreSQL...
[SUCCESS] PostgreSQL Helm 部署完成

[INFO] 部署 Vector 数据管道...
[SUCCESS] Vector Helm 部署完成

[INFO] 部署监控系统...
  [SUCCESS] Prometheus 部署完成
  [SUCCESS] Grafana 部署完成

[INFO] 等待服务就绪...
  [SUCCESS] PostgreSQL 已就绪
  [SUCCESS] Redis 已就绪
  [SUCCESS] Prometheus 已就绪
  [SUCCESS] Grafana 已就绪
[SUCCESS] 所有服务已就绪 ✓

╔══════════════════════════════════════════════════════════════╗
║                    🎉 部署完成！                             ║
╚══════════════════════════════════════════════════════════════╝

📊 服务访问信息:

  🗄️  PostgreSQL:
      内部地址: postgresql-service.postgresql-all-in-one.svc.cluster.local:5432
      用户名: postgres
      密码: postgres123
      数据库: allinone

  📊 Grafana:
      访问地址: http://localhost:30000
      用户名: admin
      密码: admin123

  📈 Prometheus:
      访问地址: http://localhost:30090
```

### 步骤3: 设置端口转发（可选）

如果需要从本地访问服务：

```bash
# PostgreSQL
kubectl port-forward -n postgresql-all-in-one svc/postgresql-service 5432:5432

# Grafana
kubectl port-forward -n postgresql-all-in-one svc/grafana 3000:3000

# Prometheus
kubectl port-forward -n postgresql-all-in-one svc/prometheus 9090:9090
```

---

## ✅ 验证部署

### 1. 检查Pod状态

```bash
kubectl get pods -n postgresql-all-in-one
```

**预期输出：**

```text
NAME                          READY   STATUS    RESTARTS   AGE
postgresql-all-in-one-0       1/1     Running   0          2m
redis-xxx                     1/1     Running   0          2m
prometheus-xxx                1/1     Running   0          2m
grafana-xxx                   1/1     Running   0          2m
vector-xxx                    1/1     Running   0          2m
```

### 2. 运行健康检查

```bash
cd scripts
./health_check.sh
```

**预期输出：**

```text
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║     PostgreSQL All-in-One 健康检查工具                      ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝

═══════════════════════════════════════════════════════════════
  1. 检查命名空间
═══════════════════════════════════════════════════════════════

[✓] 命名空间 'postgresql-all-in-one' 存在

═══════════════════════════════════════════════════════════════
  2. 检查 PostgreSQL
═══════════════════════════════════════════════════════════════

[✓] PostgreSQL StatefulSet 运行正常 (1/1)
[✓] Pod 状态: Running
[✓] PostgreSQL Service 存在

...

═══════════════════════════════════════════════════════════════
  健康检查汇总
═══════════════════════════════════════════════════════════════

  总检查项: 15
  通过: 15
  警告: 0
  失败: 0

  整体健康度: 100% - 优秀

[SUCCESS] 所有检查项通过！系统运行正常 ✓
```

### 3. 测试数据库连接

```bash
# 使用kubectl连接
kubectl exec -it -n postgresql-all-in-one statefulset/postgresql-all-in-one -- psql -U postgres -d allinone

# 在psql中执行
\l                    # 列出所有数据库
\dt                   # 列出所有表
SELECT version();     # 查看版本
\q                    # 退出
```

### 4. 访问监控面板

打开浏览器访问：

- **Grafana**: <http://localhost:3000>
  - 用户名: `admin`
  - 密码: `admin123`
  
- **Prometheus**: <http://localhost:9090>

---

## 📖 基本使用

### 1. 创建数据库表

```bash
kubectl exec -it -n postgresql-all-in-one statefulset/postgresql-all-in-one -- psql -U postgres -d allinone <<EOF
-- 创建应用日志表
CREATE TABLE IF NOT EXISTS application_logs (
    id SERIAL PRIMARY KEY,
    timestamp TIMESTAMPTZ NOT NULL,
    level VARCHAR(10) NOT NULL,
    service VARCHAR(50) NOT NULL,
    message TEXT NOT NULL,
    metadata JSONB
);

-- 创建系统指标表
CREATE TABLE IF NOT EXISTS system_metrics (
    id SERIAL PRIMARY KEY,
    timestamp TIMESTAMPTZ NOT NULL,
    metric_name VARCHAR(100) NOT NULL,
    metric_value DOUBLE PRECISION NOT NULL,
    host VARCHAR(100) NOT NULL,
    tags JSONB
);

-- 创建索引
CREATE INDEX idx_logs_timestamp ON application_logs(timestamp);
CREATE INDEX idx_logs_level ON application_logs(level);
CREATE INDEX idx_metrics_timestamp ON system_metrics(timestamp);
CREATE INDEX idx_metrics_name ON system_metrics(metric_name);

-- 启用TimescaleDB扩展（如果使用时序数据）
CREATE EXTENSION IF NOT EXISTS timescaledb;
SELECT create_hypertable('application_logs', 'timestamp');
SELECT create_hypertable('system_metrics', 'timestamp');
EOF
```

### 2. 插入测试数据

```bash
kubectl exec -it -n postgresql-all-in-one statefulset/postgresql-all-in-one -- psql -U postgres -d allinone <<EOF
-- 插入示例日志
INSERT INTO application_logs (timestamp, level, service, message, metadata) VALUES
(NOW(), 'INFO', 'api-service', 'Application started', '{"version": "1.0.0"}'),
(NOW(), 'ERROR', 'api-service', 'Database connection failed', '{"error_code": "DB001"}'),
(NOW(), 'WARN', 'worker-service', 'High memory usage detected', '{"memory_usage": "85%"}');

-- 插入示例指标
INSERT INTO system_metrics (timestamp, metric_name, metric_value, host, tags) VALUES
(NOW(), 'cpu_usage', 45.5, 'host-01', '{"datacenter": "us-east-1"}'),
(NOW(), 'memory_usage', 78.2, 'host-01', '{"datacenter": "us-east-1"}'),
(NOW(), 'disk_io', 120.5, 'host-01', '{"datacenter": "us-east-1"}');

-- 查询数据
SELECT * FROM application_logs ORDER BY timestamp DESC LIMIT 10;
SELECT * FROM system_metrics ORDER BY timestamp DESC LIMIT 10;
EOF
```

### 3. 使用Redis缓存

```bash
# 连接到Redis
kubectl exec -it -n postgresql-all-in-one deployment/redis -- redis-cli

# Redis命令
> SET mykey "Hello World"
> GET mykey
> KEYS *
> DEL mykey
> EXIT
```

### 4. 查看监控指标

访问 Grafana (<http://localhost:3000>):

1. 使用 `admin/admin123` 登录
2. 导航到 Dashboards
3. 选择 "PostgreSQL All-in-One Dashboard"
4. 查看实时性能指标：
   - 数据库连接数
   - 查询性能
   - 缓存命中率
   - CPU/内存使用

---

## 🔧 常见问题

### 问题1: Pod启动失败

**症状：** Pod状态显示 `CrashLoopBackOff` 或 `Error`

**解决方案：**

```bash
# 查看Pod详情
kubectl describe pod <pod-name> -n postgresql-all-in-one

# 查看日志
kubectl logs <pod-name> -n postgresql-all-in-one

# 常见原因和解决方法：
# 1. 资源不足 - 增加集群资源
# 2. 镜像拉取失败 - 检查网络连接
# 3. 配置错误 - 检查ConfigMap和Secret
```

### 问题2: 无法连接到服务

**症状：** 端口转发失败或无法访问服务

**解决方案：**

```bash
# 检查服务状态
kubectl get svc -n postgresql-all-in-one

# 检查端点
kubectl get endpoints -n postgresql-all-in-one

# 重新设置端口转发
kubectl port-forward -n postgresql-all-in-one svc/postgresql-service 5432:5432
```

### 问题3: 存储空间不足

**症状：** PVC状态显示 `Pending` 或存储错误

**解决方案：**

```bash
# 检查PVC状态
kubectl get pvc -n postgresql-all-in-one

# 检查存储类
kubectl get storageclass

# 如果使用Minikube，启用存储插件
minikube addons enable storage-provisioner
```

### 问题4: 性能较慢

**症状：** 查询响应时间长

**解决方案：**

```bash
# 运行性能监控
cd scripts
./performance_monitor.sh

# 检查资源使用
kubectl top pods -n postgresql-all-in-one

# 调整资源限制
kubectl edit deployment <deployment-name> -n postgresql-all-in-one
```

### 问题5: 卸载后重新部署失败

**症状：** PVC或PV仍然存在

**解决方案：**

```bash
# 完全卸载（包括清理孤立资源）
cd scripts
./undeploy.sh --force-cleanup

# 等待所有资源删除
kubectl get all -n postgresql-all-in-one

# 重新部署
./deploy.sh
```

---

## 🔄 日常运维

### 备份数据

```bash
cd scripts

# 完整备份
./backup.sh

# 只备份PostgreSQL
./backup.sh --postgresql

# 指定备份目录
./backup.sh --backup-dir /mnt/backups
```

### 恢复数据

```bash
cd scripts

# 列出可用备份
./restore.sh --list

# 完整恢复（使用最新备份）
./restore.sh --backup-dir ./backups

# 只恢复PostgreSQL
./restore.sh --postgresql --backup-dir ./backups
```

### 性能监控

```bash
cd scripts

# 一次性检查
./performance_monitor.sh

# 持续监控（30秒刷新）
./performance_monitor.sh --continuous --interval 30

# 包含日志和事件
./performance_monitor.sh --logs --events
```

### 健康检查

```bash
cd scripts

# 标准检查
./health_check.sh

# 快速检查
./health_check.sh --quick

# 详细检查（包含连接测试）
./health_check.sh --detailed --events
```

---

## 🎓 下一步

### 学习资源

1. **架构深入了解**
   - 阅读 [架构设计方案](PostgreSQL_All_in_One_架构设计方案_2025.md)
   - 了解 [Vector集成方案](PostgreSQL_All_in_One_Vector集成方案_2025.md)

2. **性能优化**
   - 学习 [性能优化与调优指南](PostgreSQL_All_in_One_性能优化与调优指南_2025.md)
   - 查看 [测试框架与基准测试](PostgreSQL_All_in_One_测试框架与基准测试_2025.md)

3. **源代码开发**
   - 参考 [源代码实现规划](PostgreSQL_All_in_One_源代码实现规划_2025.md)
   - 使用 [实现示例与代码模板](PostgreSQL_All_in_One_实现示例与代码模板_2025.md)

4. **监控和告警**
   - 配置 [监控面板与告警](PostgreSQL_All_in_One_监控面板与告警配置_2025.md)

### 实践项目

1. **数据导入**

   ```bash
   # 导入CSV数据
   kubectl exec -it -n postgresql-all-in-one statefulset/postgresql-all-in-one -- \
     psql -U postgres -d allinone -c "\COPY mytable FROM '/tmp/data.csv' WITH (FORMAT csv, HEADER true);"
   ```

2. **定时任务**

   ```bash
   # 创建定时备份CronJob
   kubectl apply -f - <<EOF
   apiVersion: batch/v1
   kind: CronJob
   metadata:
     name: postgresql-backup
     namespace: postgresql-all-in-one
   spec:
     schedule: "0 2 * * *"  # 每天凌晨2点
     jobTemplate:
       spec:
         template:
           spec:
             containers:
             - name: backup
               image: postgres:15
               command: ["pg_dump"]
               args: ["-U", "postgres", "-d", "allinone", "-f", "/backup/backup.sql"]
             restartPolicy: OnFailure
   EOF
   ```

3. **自定义仪表板**
   - 访问 Grafana
   - 创建新的Dashboard
   - 添加自定义Panel和查询

### 生产环境部署

当准备好部署到生产环境时：

1. **安全加固**
   - 修改默认密码
   - 启用TLS/SSL
   - 配置网络策略
   - 设置RBAC

2. **高可用配置**
   - 配置主从复制
   - 设置自动故障转移
   - 配置负载均衡

3. **监控告警**
   - 配置AlertManager
   - 设置通知渠道（邮件、Slack等）
   - 定义告警规则

4. **备份策略**
   - 配置自动备份
   - 设置异地备份
   - 定期测试恢复流程

---

## 📞 获取帮助

### 文档

- [项目README](PostgreSQL_All_in_One_README_2025.md)
- [项目完成总结](PostgreSQL_All_in_One_项目完成总结_2025.md)
- [项目交付清单](PostgreSQL_All_in_One_项目交付清单与部署指南_2025.md)

### 社区

- GitHub Issues: [提交问题](https://github.com/your-org/postgresql-allinone/issues)
- GitHub Discussions: [技术讨论](https://github.com/your-org/postgresql-allinone/discussions)
- Email: <support@postgresql-allinone.com>

### 贡献

欢迎贡献代码、文档或报告问题！请参阅 [CONTRIBUTING.md](../CONTRIBUTING.md)

---

## 🎉 恭喜

你已经成功部署了 PostgreSQL All-in-One 系统！

现在你可以：

- ✅ 使用高性能的PostgreSQL数据库
- ✅ 利用Redis缓存加速查询
- ✅ 通过Vector处理实时数据流
- ✅ 使用Grafana监控系统性能
- ✅ 享受简化的运维体验

**开始构建你的应用吧！** 🚀

---

*PostgreSQL All-in-One - 为中小型团队打造的经济高效、技术先进、易于维护的数据处理平台*:

*最后更新: 2025-10-08*:
