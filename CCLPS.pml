mtype = {
    EMPTY, READY, FILLED, // vessel_state notifications (OutValveCtrl -> InValveCtrl) over Red channel
    STATUS_QUERY, REQ_FILLING, FILLING, // from InValveCtrl to OutValveCtrl over Blue channel
    STATUS_QUERY_ACK, REQ_FILLING_ACK, FILLING_ACK, ATTENTION, // from OutValveCtrl to InValveCtrl over Blue channel
    OPEN, CLOSE, // commands from controllers to valves over In_cmd and Out_cmd channels
    LIQUID_QUERY // query message (InValveCtrl -> InValve) - reply comes via FromInValve channel
};

// as per handout
#define liquid 1 // liquid as a constant (value irrelevant)
chan Vessel = [2] of {bit};

// controller-to-controller channels
chan Blue = [2] of {mtype}; // bi-directional
chan Red = [2] of {mtype}; // unidirectional (OutValveCtrl -> InValveCtrl)

// controller-to-valve command channels (synchronous / unbuffered)
chan In_cmd = [0] of {mtype};
chan Out_cmd = [0] of {mtype};

chan ToInValve = [0] of {mtype}; // from InValveCtrl to InValve (synchronous: prevent queueing of LIQUID_QUERY requests)
chan FromInValve = [1] of {bit}; // InValve reports to InValveCtrl

proctype InValveCtrl(chan blue; chan red; chan in_cmd; chan toInValve; chan fromInValve) {

    mtype current_state;
    bool liquid_detection = true; // ON at start

    do 
    :: blue?ATTENTION -> // receive alert from OutValveCtrl
        liquid_detection = true;
        printf("[in controller] (blue) received ATTENTION\n");

    :: liquid_detection ->
        // request a liquid report from InValve
        toInValve!LIQUID_QUERY;
        printf("[in controller] sent LIQUID_QUERY\n");

        fromInValve?liquid;
        printf("[in controller] received LIQUID report\n");

        liquid_detection = false; // OFF until next ATTENTION

        // ------ protocol with OutValveCtrl ------ //
        blue!STATUS_QUERY;
        printf("[in controller] (blue) sent status query\n");

        blue?STATUS_QUERY_ACK;
        printf("[in controller] (blue) received status query ack\n");

        red?current_state;
        printf("[in controller] (red) received vessel state: %d\n", current_state);

        if
        :: current_state == EMPTY -> // start filling cycle only if vessel is EMPTY
            blue!REQ_FILLING;
            printf("[in controller] (blue) sent filling request\n");

            blue?REQ_FILLING_ACK;
            printf("[in controller] (blue) received filling request ack\n");

            red?READY;
            printf("[in controller] (red) received ready\n");
            current_state = READY; // keep a local view of phase for debugging

            in_cmd!OPEN;
            printf("[in controller] (in_cmd) sent OPEN\n");

            blue!FILLING;
            printf("[in controller] (blue) sent filling\n");

            blue?FILLING_ACK;
            printf("[in controller] (blue) received filling ack\n");

            red?FILLED;
            printf("[in controller] (red) received filled\n");
            current_state = FILLED; // keep a local view of phase for debugging

            // consume EMPTY so it doesn't remain queued on red and block the next READY
            red?EMPTY;
            printf("[in controller] (red) received empty\n");

            in_cmd!CLOSE;
            printf("[in controller] (in_cmd) sent CLOSE\n");
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
        printf("[out controller] (out_cmd) sent CLOSE\n");

        vessel_state = READY;
        
        red!READY;
        printf("[out controller] (red) sent READY\n");

    :: blue?FILLING ->
        printf("[out controller] (blue) received filling\n");

        blue!FILLING_ACK;
        printf("[out controller] (blue) sent filling ack\n");

        // wait until vessel is filled
        do
        :: len(vessel) == 1 -> break
        od; // removed else -> skip to prevent infinite inner looping

        vessel_state = FILLED;

        red!FILLED;
        printf("[out controller] (red) sent FILLED\n");

        out_cmd!OPEN;
        printf("[out controller] (out_cmd) sent OPEN\n");

        // wait until vessel is emptied
        do
        :: len(vessel) == 0 -> break
        od; // removed else -> skip to prevent infinite inner looping

        out_cmd!CLOSE;
        printf("[out controller] (out_cmd) sent CLOSE\n");

        vessel_state = EMPTY;
        red!EMPTY;
        printf("[out controller] (red) sent EMPTY\n");

        // notify InValveCtrl that emptying is done
        blue!ATTENTION;
        printf("[out controller] (blue) sent ATTENTION\n");
    od
}

/*
 * Assumptions:
 * 1) InValve always holds liquid.
 * 2) Only 1 batch is necessary for filling the vessel.
 */
proctype InValve(chan outflow; chan in_cmd; chan toInValve; chan fromInValve) {

    mtype state = CLOSE;
    mtype cmd;

    do
    :: in_cmd?cmd -> // listen for commands
        if
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    :: toInValve?LIQUID_QUERY ->
        // assumption: InValve always holds liquid 
        fromInValve!liquid;
        printf("[InValve] replied liquid\n");

    :: state == OPEN && len(outflow) == 0 ->
        outflow!liquid
    od
}

proctype OutValve(chan inflow; chan out_cmd) {
    
    mtype state = CLOSE;
    mtype cmd;

    do
    :: out_cmd?cmd -> // listen for commands
        if
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    // drain liquid when OutValve is OPEN and there is liquid in the vessel
    :: state == OPEN && len(inflow) > 0 ->
        inflow?liquid
    od
}

init {
    atomic { // ensure all processes are created before execution begins
        run InValveCtrl(Blue, Red, In_cmd, ToInValve, FromInValve);
        run OutValveCtrl(Blue, Red, Out_cmd, Vessel);
        run InValve(Vessel, In_cmd, ToInValve, FromInValve);
        run OutValve(Vessel, Out_cmd);
    }
}

ltl p1 {[] <> (len(Vessel) == 1)} // Vessel is filled infinitely often
ltl p2 {[] <> (len(Vessel) == 0)} // Vessel is emptied infinitely often