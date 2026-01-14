mtype = {
    EMPTY, READY, FILLED, // vessel state from OutValveCtrl to InValveCtrl over red channel
    STATUS_QUERY, REQ_FILLING, FILLING, // from InValveCtrl to OutValveCtrl over blue channel
    STATUS_QUERY_ACK, REQ_FILLING_ACK, FILLING_ACK, ATTENTION, // from OutValveCtrl to InValveCtrl over blue channel
    OPEN, CLOSE, // commands from controllers to valves over out_cmd and in_cmd channels
    LIQUID_QUERY // from InValveCtrl to InValve
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

chan toInValve = [0] of {mtype}; // InValveCtrl queries InValve
chan fromInValve = [1] of {bit}; // InValve reports to InValveCtrl

proctype InValveCtrl() {

    mtype current_state;
    mtype query;
    bool liquid_detection = true;

    do
    :: blue?ATTENTION -> // respond to attention: allow new start after purification process ends
    liquid_detection = true; // ON at start

    :: liquid_detection ->
        // query InValve for liquid
        toInValve!LIQUID_QUERY;
        printf("[in controller] (toInValve) sent LIQUID_QUERY\n");

        if
        :: fromInValve?[liquid] -> // peek for liquid (token not consumed)
            printf("[in controller] (fromInValve) liquid detected\n");
            liquid_detection = false;

            // send STATUS_QUERY to OutValveCtrl
            blue!STATUS_QUERY;
            printf("[in controller] (blue) sent STATUS_QUERY\n");

            // wait for STATUS_QUERY_ACK and current_state
            blue?STATUS_QUERY_ACK;
            printf("[in controller] (blue) received STATUS_QUERY_ACK\n");

            // receive current_state
            red?current_state;
            printf("[in controller] (red) received current_state: %d\n", current_state);

            if
            :: current_state == EMPTY ->
                // send REQ_FILLING to OutValveCtrl
                blue!REQ_FILLING;
                printf("[in controller] (blue) sent REQ_FILLING\n");

                // wait for REQ_FILLING_ACK
                blue?REQ_FILLING_ACK;
                printf("[in controller] (blue) received REQ_FILLING_ACK\n");

                // wait for READY
                red?READY;
                printf("[in controller] (red) received READY\n");

                // send command OPEN to InValve
                in_cmd!OPEN;
                printf("[in controller] (in_cmd) sent OPEN\n");

                // notify FILLING
                blue!FILLING;
                printf("[in controller] (blue) sent FILLING\n");

                // wait for FILLING_ACK
                blue?FILLING_ACK;
                printf("[in controller] (blue) received FILLING_ACK\n");

                // wait for FILLED
                red?FILLED;
                printf("[in controller] (red) received FILLED\n");

                // send command CLOSE to InValve
                in_cmd!CLOSE;
                printf("[in controller] (in_cmd) sent CLOSE\n");

            :: else -> skip // do nothing if not EMPTY
            fi

        :: else -> skip // wait for liquid to be reported
        fi
    od
}








/* 
    * Assumptions
    * 1. InValve always holds liquid.
    * 2. only 1 batch is necessary for filling the vessel
*/
proctype InValve() {

    mtype state = CLOSE;
    mtype cmd;
    mtype query;

    do
    :: in_cmd?cmd -> // listen for command
        if 
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    :: toInValve?LIQUID_QUERY -> // listen for liquid query
        if
        :: len(fromInValve) == 0 -> 
            fromInValve!liquid; //assumption: InValve always has liquid
            printf("[InValve] reported liquid present\n");
        :: else -> skip
        fi

    :: state == OPEN && len(outflow) == 0 -> // send liquid if valve is OPEN and outflow is empty
        outflow!liquid
    od
}

proctype OutValve(chan inflow, chan out_cmd) {

    mtype state = CLOSE;
    mtype cmd;

    do
    :: out_cmd?cmd -> // listen for command
        if
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    :: state == OPEN && len(inflow) > 0 -> // pour liquid if valve is OPEN and inflow channel has liquid
        inflow?liquid
    od
}

init {
    atomic {
        fromInValve!liquid; // assumption: InValve always has liquid (uncontrollable)
        run InValveCtrl();
        // run OutValveCtrl();
        run InValve();
        run OutValve(Vessel, Out_cmd);
    }
}

ltl p1 {[] <> (len(Vessel) == 1)} // Vessel is eventually filled
ltl p2 {[] <> (len(Vessel) == 0)} // Vessel is eventually emptied
