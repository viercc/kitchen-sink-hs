#!/usr/bin/env bash
echo Running all scripts in this directory...
mkdir -p ./logs
for scriptfile in *.hs *.lhs; do
    echo $scriptfile
    # These script contain infinitely-looping one
    # send SIGINT after 1 minutes
    # 'timeout' sets error status to 124 if the command is timed out
    timeout -s SIGINT 1m\
            cabal run -v0 -O0 $scriptfile >./logs/${scriptfile}.stdout
    status=$?
    if [ $status -ne 0 -a $status -ne 124 ]; then
        echo "ERROR: $status"
        exit 1
    fi
done
