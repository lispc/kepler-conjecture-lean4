#!/bin/bash
# 跨车道 lake 构建锁（2026-10-27 重建版；原 /tmp 版毁于 10-26 18:00 死机重启）
# 语义与原版一致：mkdir 原子锁 + 心跳续持 + 30min TTL 陈旧接管 + 内存闸(空闲>=50%)
#   + 1h 获取超时。用法: source <this> && lock_build nice -n 19 lake build <target>
LOCK="${KEPLER_LOCK_DIR:-/tmp/kepler_build_lock.dir}"
HOLD=1800          # 30min：心跳停止超此时长的锁视为死锁，可接管
ACQ_TIMEOUT=3600   # 1h 获取超时
MEM_MIN=50

mem_free_pct() {
  memory_pressure -Q 2>/dev/null | tail -1 | sed -n 's/.*free percentage: \([0-9]*\)%.*/\1/p'
}

acquire() {
  local waited=0 now ts
  while true; do
    if mkdir "$LOCK" 2>/dev/null; then echo $$ > "$LOCK/pid"; date +%s > "$LOCK/ts"; return 0; fi
    now=$(date +%s); ts=$(cat "$LOCK/ts" 2>/dev/null || echo "$now")
    if [ $((now - ts)) -gt "$HOLD" ]; then rm -rf "$LOCK"; continue; fi
    if [ "$waited" -ge "$ACQ_TIMEOUT" ]; then echo "LOCK ACQUIRE TIMEOUT ${ACQ_TIMEOUT}s (holder pid $(cat "$LOCK/pid" 2>/dev/null))" >&2; return 1; fi
    sleep 30; waited=$((waited + 30))
  done
}

heartbeat() { while :; do date +%s > "$LOCK/ts" 2>/dev/null || return; sleep 60; done; }

lock_build() {
  acquire || return 1
  local pct; pct=$(mem_free_pct)
  if [ "${pct:-0}" -lt "$MEM_MIN" ]; then
    echo "MEM FREE < ${MEM_MIN}%, sleeping 60s" >&2
    sleep 60
    pct=$(mem_free_pct)
    if [ "${pct:-0}" -lt "$MEM_MIN" ]; then echo "MEM STILL LOW, abort build" >&2; rm -rf "$LOCK"; return 3; fi
  fi
  heartbeat & local hb=$!
  "$@"
  local rc=$?
  kill "$hb" 2>/dev/null
  rm -rf "$LOCK"
  return $rc
}
