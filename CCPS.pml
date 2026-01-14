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

proctype InValveCtrl(chan blue, chan red, chan in_cmd, chan toInValve, chan fromInValve) {

    mtype current_state;
    mtype q;
    bool liquid_detection = true;

    do
    :: blue?ATTENTION -> // listen for ATTENTION
        // allow new start after purification process ends
        liquid_detection = true // ON at start

    :: liquid_detection ->
        // query InValve for liquid
        toInValve!LIQUID_QUERY;
        printf("[in controller] (toInValve) sent LIQUID_QUERY\n")

        if
        :: fromInValve?[liquid] ->
            liquid_detection = false;

            // Query OutValveCtrl for vessel state
            blue!STATUS_QUERY;
            blue?STATUS_QUERY_ACK;
            red?current_state;

            if
            :: current_state == EMPTY ->
                blue!REQ_FILLING;
                blue?REQ_FILLING_ACK;

                red?READY;

                // send command OPEN to InValve
                in_cmd!OPEN;

                // notify FILLING
                blue!FILLING;
                blue?FILLING_ACK;

                // wait for FILLED
                red?FILLED;

                // send command CLOSE to InValve
                in_cmd!CLOSE
            :: else -> skip
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
proctype InValve(chan outflow,
                 chan in_cmd,
                 chan toInValve, chan fromInValve)
{
    mtype state = CLOSE;
    mtype cmd;
    mtype q;

    do
    :: in_cmd?cmd ->
        if
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    :: toInValve?q ->
        if
        :: q == LIQUID_QUERY ->
            if
            :: len(fromInValve) == 0 -> fromInValve!liquid
            :: else -> skip
            fi
        :: else -> skip
        fi

    :: state == OPEN && len(outflow) == 0 ->
        outflow!liquid
    od
}

proctype OutValve(chan inflow, chan out_cmd)
{
    mtype state = CLOSE;
    mtype cmd;

    do
    :: out_cmd?cmd ->
        if
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    :: state == OPEN && len(inflow) > 0 ->
        inflow?liquid
    od
}

init {
    atomic {
        run InValveCtrl(blue, red, in_cmd, toInValve, fromInValve);
        run OutValveCtrl(blue, red, out_cmd);
        run InValve(Vessel, in_cmd, toInValve, fromInValve);
        run OutValve(Vessel, out_cmd);
    }
}

ltl p_fill {[] <> (len(Vessel) == 1)} // Vessel is eventually filled
ltl p_empty {[] <> (len(Vessel) == 0)} // Vessel is eventually emptied