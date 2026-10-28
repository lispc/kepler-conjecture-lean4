#!/bin/bash
# integrate_lane.sh — 车道快照 → 主仓 落库流水线（队列 §3 第 5 项固化）
# 由 tooling-w1 车道交付；正本由编排者验收后落库 scripts/integrate_lane.sh。
#
# 流水线：MD5 校验 → cp+git add → diff 断言 → 闸(auto_gate) → pathspec 提交
#         → push → 收尾清单打印。
# 根除两坑：
#   坑① 后台 shell cwd 重置致闸 127 空跑 —— 全脚本零 cd（唯一 cd 在闸子壳
#        内、与调用同壳紧邻，且调用前用绝对路径验证闸/锁脚本存在）；
#        一切 git 走 `git -C "$REPO"`。
#   坑② 裸 `git commit` 误提他人 staged 件 —— 提交永不裸奔，一律
#        `git commit -F <msgfile> -- <targets...>` pathspec 限定。
#
# 环境变量:
#   INTEGRATE_REPO     指向目标 git 仓根（缺省 = 本脚本所在仓根）。
#                      沙盒测试/真实快照演练必须用它指向沙盒仓——
#                      --dry-run 会真实执行步骤 1-3（含 cp/add），并非只读。
#   KEPLER_LOCK_DIR    透传给 kepler_build_lock.sh（沙盒测试重定向锁目录）。
# rc 码表: 0 成功/演练完成/无可落库  2 用法错  3 预检失败(仓/快照/manifest/
#   目标父目录缺失/闸脚本缺失)  4 MD5 不符  5 diff 漂移断言  6 cp/add 失败
#   7 闸未过  8 提交失败  9 push 失败
# 边界: 本脚本只管普通落库；STATEMENT-FIX(GATE_MODE)/DEF-FIX 专用链不在范围。

set -u
PROG="integrate_lane.sh"
TAB="$(printf '\t')"

usage() {
  cat <<'USAGE'
用法: integrate_lane.sh --snapshot <lane快照目录> --manifest <映射表>
                        --lane-files <逗号分隔,lean/起> --thm <闸THM>
                        [--commit-msg <文件|字符串>] [--docs-only] [--dry-run]

manifest 行格式: <快照相对路径><TAB><仓内目标路径>（# 与空行忽略）。
目标两模式由仓态自动判定：目标不在 HEAD = 纯追加(新文件)；在 HEAD = 预期替换。
--docs-only 时 --lane-files/--thm 可省（闸整段跳过）。
USAGE
}

die() { rc="$1"; shift; echo "$PROG: FATAL(rc=$rc): $*" >&2; exit "$rc"; }
info() { echo "[$PROG] $*"; }
usage_die() { rc="$1"; shift; usage >&2; echo >&2; die "$rc" "$@"; }

# ---------- 参数解析 ----------
SNAPSHOT=""; MANIFEST=""; LANE_FILES=""; THM=""; COMMIT_MSG_ARG=""
DOCS_ONLY=0; DRY_RUN=0

while [ $# -gt 0 ]; do
  case "$1" in
    --snapshot|--manifest|--lane-files|--thm|--commit-msg)
      [ $# -ge 2 ] || usage_die 2 "$1 缺少值"
      case "$1" in
        --snapshot)    SNAPSHOT="$2" ;;
        --manifest)    MANIFEST="$2" ;;
        --lane-files)  LANE_FILES="$2" ;;
        --thm)         THM="$2" ;;
        --commit-msg)  COMMIT_MSG_ARG="$2" ;;
      esac
      shift 2 ;;
    --docs-only) DOCS_ONLY=1; shift ;;
    --dry-run)   DRY_RUN=1; shift ;;
    -h|--help)   usage; exit 0 ;;
    *)           usage_die 2 "未知参数: $1" ;;
  esac
done

[ -n "$SNAPSHOT" ] || usage_die 2 "缺 --snapshot"
[ -n "$MANIFEST" ] || usage_die 2 "缺 --manifest"
if [ "$DOCS_ONLY" -eq 0 ]; then
  [ -n "$LANE_FILES" ] || usage_die 2 "缺 --lane-files（闸白名单）"
  [ -n "$THM" ]        || usage_die 2 "缺 --thm（闸 THM）"
fi

# ---------- 目标仓裁定（缺省=脚本所在仓根） ----------
if [ -n "${INTEGRATE_REPO:-}" ]; then
  REPO="$INTEGRATE_REPO"
else
  REPO="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel 2>/dev/null)" \
    || usage_die 2 "无法定位目标仓：请设 INTEGRATE_REPO 或把本脚本放入仓内"
fi
REPO="$(cd "$REPO" && pwd)" || die 3 "INTEGRATE_REPO 不存在: $REPO"
git -C "$REPO" rev-parse --show-toplevel >/dev/null 2>&1 || die 3 "目标不是 git 仓: $REPO"
git -C "$REPO" rev-parse --verify HEAD >/dev/null 2>&1 || die 3 "目标仓无任何提交（无 HEAD 基线）: $REPO"
BASELINE="$(git -C "$REPO" rev-parse --short HEAD)"

[ -d "$SNAPSHOT" ] || die 3 "快照目录不存在: $SNAPSHOT"
SNAPSHOT="$(cd "$SNAPSHOT" && pwd)"
[ -f "$MANIFEST" ] || die 3 "manifest 不存在: $MANIFEST"
LANE="$(basename "$SNAPSHOT")"
info "目标仓 ${REPO}（基线 HEAD ${BASELINE}）；快照 ${SNAPSHOT}（车道 ${LANE}）"
if [ "$DRY_RUN" -eq 1 ]; then
  info "--dry-run：步骤 1-3 真实执行（会写入目标仓工作树！），步骤 4-6 仅打印"
fi

# ---------- 解析 manifest：预检 + 收集（一切写入发生之前） ----------
SRCS_A=(); DSTS_A=(); MODES_A=()
N=0; N_APPEND=0; N_REPLACE=0
while IFS= read -r line || [ -n "$line" ]; do
  case "$line" in ""|\#*) continue ;; esac
  case "$line" in
    *"$TAB"*) : ;;
    *) die 3 "manifest 第 $((N+1)) 数据行缺 TAB 分隔: $line" ;;
  esac
  src="${line%%"$TAB"*}"
  rest="${line#*"$TAB"}"
  dst="${rest%%"$TAB"*}"
  extra="${rest#*"$TAB"}"
  [ "$extra" = "$dst" ] || die 3 "manifest 行字段超两列: $line"
  [ -n "$src" ] && [ -n "$dst" ] || die 3 "manifest 行有空字段: $line"
  case "$dst" in /*) die 3 "目标路径须为仓相对路径: $dst" ;; esac
  case "$dst" in *..*) die 3 "目标路径含 ..: $dst" ;; esac
  [ -f "$SNAPSHOT/$src" ] || die 3 "快照文件缺失: $SNAPSHOT/$src"
  # 预检：目标父目录必须在仓内存在（防 cp 铸出新目录结构 / 错路径落库）
  dst_parent="$(dirname "$dst")"
  [ -d "$REPO/$dst_parent" ] \
    || die 3 "目标父目录在仓内不存在: $dst （快照与仓结构分叉？检查 manifest）"
  # 预检 + 模式判定：在 HEAD = 预期替换；不在 = 纯追加（新文件）
  if git -C "$REPO" cat-file -e "HEAD:$dst" 2>/dev/null; then
    mode="replace"
    [ -f "$REPO/$dst" ] || die 5 "预期替换目标在工作树缺失（未提交的删除？）: $dst"
    git -C "$REPO" show "HEAD:$dst" | cmp -s - "$REPO/$dst" \
      || die 5 "工作树相对 HEAD 已有未提交改动（他人产物，cp 将覆盖）: $dst"
    git -C "$REPO" diff --cached --quiet -- "$dst" \
      || die 5 "该路径已有人 staged 备件（cp+提交将丢弃之）: $dst"
    N_REPLACE=$((N_REPLACE+1))
  else
    mode="append"
    if [ -e "$REPO/$dst" ]; then
      die 5 "纯追加目标已存在于工作树（他人未提交产物）: $dst"
    fi
    N_APPEND=$((N_APPEND+1))
  fi
  SRCS_A+=("$src"); DSTS_A+=("$dst"); MODES_A+=("$mode")
  N=$((N+1))
done < "$MANIFEST"
[ "$N" -gt 0 ] || die 3 "manifest 无有效数据行: $MANIFEST"
info "manifest 预检通过：${N} 个目标（追加 ${N_APPEND} / 替换 ${N_REPLACE}），一切写入前校验完成"

# ---------- 步骤 1：MD5 校验 ----------
if [ -f "$SNAPSHOT/MD5SUMS" ]; then
  verified=0
  while IFS= read -r mline || [ -n "$mline" ]; do
    case "$mline" in ""|\#*) continue ;; esac
    set -f
    # shellcheck disable=SC2086
    set -- $mline
    set +f
    mhash="$1"; mpath="$2"
    [ -n "${mhash:-}" ] && [ -n "${mpath:-}" ] || die 4 "MD5SUMS 行格式异常: $mline"
    case "$mpath" in
      /*) mabs="$mpath" ;;
      *)  mabs="$SNAPSHOT/$mpath" ;;
    esac
    if [ -f "$mabs" ]; then
      actual="$(md5 -q "$mabs")"
      [ "$actual" = "$mhash" ] || die 4 "MD5 不符: ${mabs}（MD5SUMS=${mhash} 实测=${actual}）"
      verified=$((verified+1))
    else
      info "MD5 条目跳过（路径不存在，疑历史暂存路径）: $mpath"
    fi
  done < "$SNAPSHOT/MD5SUMS"
  info "步骤1 MD5 校验通过：$verified 条"
else
  info "步骤1：快照无 MD5SUMS，跳过"
fi

# ---------- 步骤 2：cp + git add（新文件不 add 则闸 rule① 不可见） ----------
i=0
while [ "$i" -lt "$N" ]; do
  src="${SRCS_A[$i]}"; dst="${DSTS_A[$i]}"; mode="${MODES_A[$i]}"
  cp "$SNAPSHOT/$src" "$REPO/$dst" || die 6 "cp 失败: $src -> $dst"
  git -C "$REPO" add -- "$dst" || die 6 "git add 失败: $dst"
  info "步骤2 [$mode] $src -> $dst （已 cp + git add）"
  i=$((i+1))
done

# ---------- 步骤 3：diff 断言（防快照与工作树分叉） ----------
total_changes=0
i=0
while [ "$i" -lt "$N" ]; do
  src="${SRCS_A[$i]}"; dst="${DSTS_A[$i]}"; mode="${MODES_A[$i]}"
  cmp -s "$SNAPSHOT/$src" "$REPO/$dst" || die 5 "cp 后逐字节断言失败: $dst"
  stats="$(git -C "$REPO" diff HEAD --numstat -- "$dst" | head -n 1)"
  adds="${stats%%"$TAB"*}"; tmp="${stats#*"$TAB"}"; dels="${tmp%%"$TAB"*}"
  case "$adds" in
    ""|-*) die 5 "diff numstat 异常（二进制或无 diff？）: $dst" ;;
  esac
  if [ "$mode" = "append" ]; then
    [ "$dels" = "0" ] || die 5 "纯追加断言失败：新文件出现删除行 ($dels): $dst"
    expect="$(awk 'END{print NR}' "$SNAPSHOT/$src")"
    [ "$adds" = "$expect" ] || die 5 "纯追加断言失败：diff +$adds 行 ≠ 快照 $expect 行: $dst"
  fi
  total_changes=$((total_changes + adds + dels))
  info "步骤3 断言通过 [$mode] $dst (+$adds/-$dels)"
  i=$((i+1))
done
info "步骤3 全部通过：$N 个目标 vs HEAD 累计 $total_changes 行变更"
if [ "$total_changes" -eq 0 ]; then
  info "所有目标与 HEAD 无差异：无可落库，正常退出（未提交未 push）"
  exit 0
fi

# ---------- 闸调用命令串（步骤 4 用；docs-only 跳过） ----------
# --lane-files 收 lean/ 起的仓根相对路径；闸要求 lean-相对，转发前剥前缀。
LANE_FILES_REL=""
if [ -n "$LANE_FILES" ]; then
  OLDIFS="$IFS"; IFS=','
  set -f
  for f in $LANE_FILES; do
    case "$f" in lean/*) f="${f#lean/}" ;; esac
    [ -n "$f" ] || continue
    if [ -n "$LANE_FILES_REL" ]; then LANE_FILES_REL="$LANE_FILES_REL,$f"; else LANE_FILES_REL="$f"; fi
  done
  set +f
  IFS="$OLDIFS"
fi
GATE_FILE="${LANE_FILES_REL%%,*}"   # 闸主文件 = 首个 lane-file（lean-相对）
GATE_CMD="(cd '$REPO/lean' && source '$REPO/lean/scripts/kepler_build_lock.sh' && LANE_FILES='$LANE_FILES_REL' THM='$THM' lock_build nice -n 19 bash scripts/auto_gate.sh '$GATE_FILE' '$THM')"

TMPMSG="$(mktemp -t integrate_lane_msg)" || die 6 "mktemp 失败"
trap 'rm -f "$TMPMSG"' EXIT
if [ -n "$COMMIT_MSG_ARG" ]; then
  if [ -f "$COMMIT_MSG_ARG" ]; then
    cp "$COMMIT_MSG_ARG" "$TMPMSG"
  else
    printf '%s\n' "$COMMIT_MSG_ARG" > "$TMPMSG"
  fi
else
  {
    echo "落库 ${LANE}：${N} 文件（integrate_lane.sh 流水线）"
    echo "- 快照: ${SNAPSHOT}（基线 HEAD ${BASELINE}）"
    if [ "$DOCS_ONLY" -eq 1 ]; then
      echo "- 闸: docs-only 模式，按规程免闸（THM 未使用）"
    else
      echo "- 闸: THM=$THM PASS（auto_gate.sh，lock_build 串行）"
    fi
    echo "- 如实披露: 本提交以 pathspec 限定，仅含 manifest 映射的以下路径，"
    echo "  不含仓内他人 staged 件；步骤 1-3（MD5/cp/diff 断言）全部通过："
    i=0; while [ "$i" -lt "$N" ]; do echo "  ${DSTS_A[$i]}"; i=$((i+1)); done
  } > "$TMPMSG"
fi

if [ "$DRY_RUN" -eq 1 ]; then
  echo "------------------------------------------------------------"
  info "--dry-run：步骤 4-6 仅打印，未执行"
  if [ "$DOCS_ONLY" -eq 1 ]; then
    echo "  (4) 闸: 跳过（docs-only）"
  else
    echo "  (4) 闸: $GATE_CMD"
  fi
  printf '  (5) git -C %s commit -F <%s> --' "$REPO" "$TMPMSG"
  i=0; while [ "$i" -lt "$N" ]; do printf ' %s' "${DSTS_A[$i]}"; i=$((i+1)); done; echo
  echo "  (6) git -C $REPO push"
  echo "------------------------------------------------------------"
  info "回退本次 dry-run 落进工作树的产物："
  i=0
  while [ "$i" -lt "$N" ]; do
    dst="${DSTS_A[$i]}"; mode="${MODES_A[$i]}"
    if [ "$mode" = "append" ]; then
      echo "  git -C '$REPO' rm --cached -q '$dst' && rm -f '$REPO/$dst'"
    else
      echo "  git -C '$REPO' checkout -q -- '$dst'"
    fi
    i=$((i+1))
  done
  info "--dry-run 完成（步骤 1-3 已真实通过）"
  exit 0
fi

# ---------- 步骤 4：闸（真实执行） ----------
if [ "$DOCS_ONLY" -eq 1 ]; then
  info "步骤4 docs-only：闸跳过"
else
  [ -f "$REPO/lean/scripts/auto_gate.sh" ] || die 3 "闸脚本缺失: $REPO/lean/scripts/auto_gate.sh"
  [ -f "$REPO/lean/scripts/kepler_build_lock.sh" ] || die 3 "锁脚本缺失: $REPO/lean/scripts/kepler_build_lock.sh"
  [ -d "$REPO/lean" ] || die 3 "$REPO/lean 不存在"
  info "步骤4 闸: $GATE_CMD"
  # 坑①防线：cd 与调用同一子壳紧邻执行；闸/锁已用绝对路径预验存在；
  # 子壳内不依赖任何外部 cwd 假设；rc 逐层透传，闸不过绝不提交。
  gatrc=0
  ( cd "$REPO/lean" || exit 3
    source "$REPO/lean/scripts/kepler_build_lock.sh" || exit 3
    LANE_FILES="$LANE_FILES_REL" THM="$THM" lock_build nice -n 19 bash scripts/auto_gate.sh "$GATE_FILE" "$THM"
  ) || gatrc=$?
  [ "$gatrc" -eq 0 ] || die 7 "闸未过（rc=${gatrc}）THM=${THM}；工作树保留待查，未提交未 push"
  info "步骤4 闸 PASS"
fi

# ---------- 步骤 5：pathspec 提交（铁律：永不裸 git commit） ----------
# 坑②防线：即便仓内有他人 staged 件，-- <targets...> 只提交本车道 manifest 路径。
info "步骤5 pathspec 提交（仅 $N 个目标路径）"
git -C "$REPO" commit -F "$TMPMSG" -- "${DSTS_A[@]}" || die 8 "git commit 失败"
NEWHASH="$(git -C "$REPO" rev-parse --short HEAD)"
info "步骤5 提交完成: $NEWHASH"

# ---------- 步骤 6：push + 收尾清单 ----------
git -C "$REPO" push || die 9 "git push 失败（提交 $NEWHASH 留在本地）"
info "步骤6 push 完成"

echo "==================== 收尾清单 ===================="
echo " [x] 落库提交 ${NEWHASH}（基线 ${BASELINE}）:"
i=0; while [ "$i" -lt "$N" ]; do echo "       ${DSTS_A[$i]}"; i=$((i+1)); done
echo " [x] push 完成"
if [ "$DOCS_ONLY" -eq 1 ]; then echo " [x] 闸: docs-only 免闸"; else echo " [x] 闸: THM=$THM PASS"; fi
echo " [ ] TSV/地图重生成：重大波次随更 docs/module-map.md 普查节；批次末重生成 DEBT.md（HANDOFF 收波清单）"
echo " [ ] queue 收波：PLAN.md §3 队列标记 $LANE 已落库 + STATUS.md 日期节记波"
echo "=================================================="
