mtype = {
    EMPTY, READY, FILLED, // vessel state from OutValveCtrl to InValveCtrl over red channel
    STATUS_QUERY, REQ_FILLING, FILLING, // from InValveCtrl to OutValveCtrl over blue channel
    STATUS_QUERY_ACK, REQ_FILLING_ACK, FILLING_ACK, ATTENTION, // from OutValveCtrl to InValveCtrl over blue channel
    OPEN, CLOSE // commands from controllers to valves over out_cmd and in_cmd channels
};

// as per handout
#define liquid 1; // liquid as a constant (value irrelevant)
chan Vessel = [2] of {bit};

// controller-to-controller channels
chan blue = [2] of {mtype};
chan red  = [2] of {mtype};

// local valve command channels (sync/unbuffered)
chan in_cmd  = [0] of {mtype};
chan out_cmd = [0] of {mtype};

// from InValve to InValveCtrl
chan fromInValve = [1] of {bit};

proctype InValveCtrl(chan blue, chan red, chan in_cmd, chan fromInValve)
{
    mtype current_state;
    bool liquid_detection = true; // ON at start

    do
    :: blue?ATTENTION ->
        // allow new start after ATTENTION
        liquid_detection = true

    :: liquid_detection && fromInValve?[liquid] ->
        // start protocol and disable further detection until reset
        liquid_detection = false;

        // send status query
        blue!STATUS_QUERY;
        printf("[in controller] (blue) sent status query\n");

        // receive status query ack
        blue?STATUS_QUERY_ACK;
        printf("[in controller] (blue) received status query ack\n");

        // receive vessel state
        red?current_state;
        printf("[in controller] (red) received vessel state: %d\n", current_state);

        if // proceed to FILLING if Vessel is EMPTY; else skip to prevent blocking
        :: current_state == EMPTY ->
            // request filling
            blue!REQ_FILLING;
            printf("[in controller] (blue) sent filling request\n");

            // receive filling request ack
            blue?REQ_FILLING_ACK;
            printf("[in controller] (blue) received filling request ack\n");

            // wait for READY
            red?READY;
            printf("[in controller] (red) received ready\n");

            // send command to OPEN valve
            in_cmd!OPEN;
            printf("[in controller] (in_cmd) sent OPEN\n");

            // notify FILLING
            blue!FILLING;
            printf("[in controller] (blue) sent filling\n");

            // receive filling ack
            blue?FILLING_ACK;
            printf("[in controller] (blue) received filling ack\n");

            // wait for FILLED
            red?FILLED;
            printf("[in controller] (red) received filled\n");

            // send command to CLOSE valve
            in_cmd!CLOSE
            printf("[in controller] (in_cmd) sent CLOSE\n");
        :: else -> skip
        fi
    od
}