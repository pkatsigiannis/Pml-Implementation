mtype = {
    EMPTY, READY, FILLED, // vessel state from OutValveCtrl to InValveCtrl over red channel
    STATUS_QUERY, REQ_FILLING, FILLING, // from InValveCtrl to OutValveCtrl over blue channel
    STATUS_QUERY_ACK, REQ_FILLING_ACK, FILLING_ACK, ATTENTION, // from OutValveCtrl to InValveCtrl over blue channel
    OPEN, CLOSE, // commands from controllers to valves over out_cmd and in_cmd channels
    LIQUID_QUERY // from InValveCtrl to InValve
};

// as per handout
#define liquid 1 // liquid as a constant (value irrelevant)
chan Vessel = [2] of {bit};

// controller-to-controller channels
chan Blue = [2] of {mtype};
chan Red = [2] of {mtype};

// local valve command channels (sync/unbuffered)
chan In_cmd = [0] of {mtype};
chan Out_cmd = [0] of {mtype};

chan ToInValve = [0] of {mtype}; // InValveCtrl queries InValve
chan FromInValve = [1] of {bit}; // InValve reports to InValveCtrl

proctype InValveCtrl(chan blue; chan red; chan in_cmd; chan toInValve; chan fromInValve) {

    mtype current_state;
    bool liquid_detection = true;

    do
    :: blue?ATTENTION ->
        liquid_detection = true

    :: liquid_detection ->
        /* Real query: request then wait for reply (consumes reply token) */
        toInValve!LIQUID_QUERY;
        printf("[in controller] sent LIQUID_QUERY\n");

        fromInValve?liquid;
        printf("[in controller] received LIQUID report\n");

        liquid_detection = false;

        /* protocol with OutValveCtrl */
        blue!STATUS_QUERY;
        printf("[in controller] (blue) sent status query\n");

        blue?STATUS_QUERY_ACK;
        printf("[in controller] (blue) received status query ack\n");

        red?current_state;
        printf("[in controller] (red) received vessel state: %d\n", current_state);

        if
        :: current_state == EMPTY ->
            blue!REQ_FILLING;
            printf("[in controller] (blue) sent filling request\n");

            blue?REQ_FILLING_ACK;
            printf("[in controller] (blue) received filling request ack\n");

            red?READY;
            printf("[in controller] (red) received ready\n");

            in_cmd!OPEN;
            printf("[in controller] (outflow) sent OPEN\n");

            blue!FILLING;
            printf("[in controller] (blue) sent filling\n");

            blue?FILLING_ACK;
            printf("[in controller] (blue) received filling ack\n");

            red?FILLED;
            printf("[in controller] (red) received filled\n");

            in_cmd!CLOSE
            printf("[in controller] (outflow) sent CLOSE\n");
        :: else -> skip
        fi
    od
}

proctype OutValveCtrl(chan blue; chan red; chan out_cmd; chan vessel) {

    mtype vessel_state = EMPTY;

    do
    :: blue?STATUS_QUERY ->
       printf("[out controller] (blue) received status query\n");

        blue!STATUS_QUERY_ACK;
        printf("[out controller] (blue) sent status query ack\n");

        red!vessel_state;
        printf("[out controller] (red) sent vessel state: %d\n", vessel_state);

    :: blue?REQ_FILLING ->
        printf("[out controller] (blue) received filling request\n");

        blue!REQ_FILLING_ACK;
        printf("[out controller] (blue) sent filling request ack\n");

        out_cmd!CLOSE;
        printf("[out controller] (outflow) sent CLOSE\n");

        vessel_state = READY;
        
        red!READY;
        printf("[out controller] (red) sent READY\n");

    :: blue?FILLING ->
        printf("[out controller] (blue) received filling\n");

        blue!FILLING_ACK;
        printf("[out controller] (blue) sent filling ack\n");

        /* wait until the one batch appears */
        do
        :: len(vessel) == 1 -> break
        :: else -> skip
        od;

        vessel_state = FILLED;

        red!FILLED;
        printf("[out controller] (red) sent FILLED\n");

        /* drain: open, wait until empty, close */
        out_cmd!OPEN;
        printf("[out controller] (outflow) sent OPEN\n");

        do
        :: len(vessel) == 0 -> break
        :: else -> skip
        od;

        out_cmd!CLOSE;
        printf("[out controller] (outflow) sent CLOSE\n");

        vessel_state = EMPTY;
        red!EMPTY;
        printf("[out controller] (red) sent EMPTY\n");

        blue!ATTENTION
        printf("[out controller] (blue) sent ATTENTION\n");
    od
}

/*
 * Assumptions:
 * 1) InValve always holds liquid.
 * 2) Only 1 batch is necessary for filling the vessel.
 *
 * Implementation: it ALWAYS replies 'liquid' to every LIQUID_QUERY.
 */
proctype InValve(chan outflow; chan in_cmd; chan toInValve; chan fromInValve)
{
    mtype state = CLOSE;
    mtype cmd;

    do
    :: in_cmd?cmd ->
        if
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    :: toInValve?LIQUID_QUERY ->
        /* always report liquid */
        fromInValve!liquid;
        printf("[InValve] replied liquid\n");

    :: state == OPEN && len(outflow) == 0 ->
        outflow!liquid
    od
}

proctype OutValve(chan inflow; chan out_cmd)
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
        run InValveCtrl(Blue, Red, In_cmd, ToInValve, FromInValve);
        run OutValveCtrl(Blue, Red, Out_cmd, Vessel);
        run InValve(Vessel, In_cmd, ToInValve, FromInValve);
        run OutValve(Vessel, Out_cmd);
    }
}

ltl p1 {[] <> (len(Vessel) == 1)} // Vessel is eventually filled
ltl p2 {[] <> (len(Vessel) == 0)} // Vessel is eventually emptied
