{{/*
Expand the name of the chart.
*/}}
{{- define "postgresql-all-in-one.name" -}}
{{- default .Chart.Name .Values.nameOverride | trunc 63 | trimSuffix "-" }}
{{- end }}

{{/*
Create a default fully qualified app name.
We truncate at 63 chars because some Kubernetes name fields are limited to this (by the DNS naming spec).
If release name contains chart name it will be used as a full name.
*/}}
{{- define "postgresql-all-in-one.fullname" -}}
{{- if .Values.fullnameOverride }}
{{- .Values.fullnameOverride | trunc 63 | trimSuffix "-" }}
{{- else }}
{{- $name := default .Chart.Name .Values.nameOverride }}
{{- if contains $name .Release.Name }}
{{- .Release.Name | trunc 63 | trimSuffix "-" }}
{{- else }}
{{- printf "%s-%s" .Release.Name $name | trunc 63 | trimSuffix "-" }}
{{- end }}
{{- end }}
{{- end }}

{{/*
Create chart name and version as used by the chart label.
*/}}
{{- define "postgresql-all-in-one.chart" -}}
{{- printf "%s-%s" .Chart.Name .Chart.Version | replace "+" "_" | trunc 63 | trimSuffix "-" }}
{{- end }}

{{/*
Common labels
*/}}
{{- define "postgresql-all-in-one.labels" -}}
helm.sh/chart: {{ include "postgresql-all-in-one.chart" . }}
{{ include "postgresql-all-in-one.selectorLabels" . }}
{{- if .Chart.AppVersion }}
app.kubernetes.io/version: {{ .Chart.AppVersion | quote }}
{{- end }}
app.kubernetes.io/managed-by: {{ .Release.Service }}
{{- end }}

{{/*
Selector labels
*/}}
{{- define "postgresql-all-in-one.selectorLabels" -}}
app.kubernetes.io/name: {{ include "postgresql-all-in-one.name" . }}
app.kubernetes.io/instance: {{ .Release.Name }}
{{- end }}

{{/*
Create the name of the service account to use
*/}}
{{- define "postgresql-all-in-one.serviceAccountName" -}}
{{- if .Values.serviceAccount.create }}
{{- default (include "postgresql-all-in-one.fullname" .) .Values.serviceAccount.name }}
{{- else }}
{{- default "default" .Values.serviceAccount.name }}
{{- end }}
{{- end }}

{{/*
Create the name of the PostgreSQL secret
*/}}
{{- define "postgresql-all-in-one.postgresqlSecretName" -}}
{{- printf "%s-postgresql-secret" (include "postgresql-all-in-one.fullname" .) }}
{{- end }}

{{/*
Create the name of the PostgreSQL config
*/}}
{{- define "postgresql-all-in-one.postgresqlConfigName" -}}
{{- printf "%s-postgresql-config" (include "postgresql-all-in-one.fullname" .) }}
{{- end }}

{{/*
Create the name of the Redis secret
*/}}
{{- define "postgresql-all-in-one.redisSecretName" -}}
{{- printf "%s-redis-secret" (include "postgresql-all-in-one.fullname" .) }}
{{- end }}

{{/*
Create the name of the Prometheus config
*/}}
{{- define "postgresql-all-in-one.prometheusConfigName" -}}
{{- printf "%s-prometheus-config" (include "postgresql-all-in-one.fullname" .) }}
{{- end }}

{{/*
Create the name of the Grafana dashboard config
*/}}
{{- define "postgresql-all-in-one.grafanaDashboardName" -}}
{{- printf "%s-grafana-dashboard" (include "postgresql-all-in-one.fullname" .) }}
{{- end }}

{{/*
Create the PostgreSQL connection string
*/}}
{{- define "postgresql-all-in-one.postgresqlConnectionString" -}}
{{- printf "postgresql://%s:%s@%s-postgresql:5432/%s" .Values.postgresql.auth.username .Values.postgresql.auth.postgresPassword (include "postgresql-all-in-one.fullname" .) .Values.postgresql.auth.database }}
{{- end }}

{{/*
Create the Redis connection string
*/}}
{{- define "postgresql-all-in-one.redisConnectionString" -}}
{{- if .Values.redis.auth.enabled }}
{{- printf "redis://:%s@%s-redis:6379/%d" .Values.redis.auth.password (include "postgresql-all-in-one.fullname" .) 0 }}
{{- else }}
{{- printf "redis://%s-redis:6379/0" (include "postgresql-all-in-one.fullname" .) }}
{{- end }}
{{- end }}
