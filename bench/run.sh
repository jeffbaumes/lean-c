#!/bin/sh
# Benchmark iteration logger. Usage: run.sh <tag> <command...>
# Runs the command unchanged (same output, same exit status) and appends one line to
# bench/logs/<tag>.log: start time, wall seconds, exit status, command.
tag="$1"; shift
log="/Users/jeff/code/lean-c/bench/logs/$tag.log"
start=$(date +%s)
"$@"
status=$?
end=$(date +%s)
printf '%s\t%ss\texit=%s\t%s\n' "$(date -r "$start" '+%Y-%m-%dT%H:%M:%S')" "$((end - start))" "$status" "$*" >> "$log"
exit $status
