#! /usr/bin/env bash
set -euo pipefail

log () {
  printf '%s\n' "$@"
}

# log OPTIND "$OPTIND"
while getopts ':ab:c' opt ; do
  # log opt "$opt" OPTIND "$OPTIND" OPTARG "${OPTARG:-}"
  case "$opt" in
    :) log "Missing required param for $OPTARG" ;;
    a) log 'Saw a' ;;
    b) log "Saw b=$OPTARG" ;;
    c) log 'Saw c' ;;
    *) log "Unsupported option $OPTARG" ;;
  esac
done
# log OPTIND "$OPTIND"
# log args "$@"
shift $((OPTIND-1))
log 'args post shift' "$@"
