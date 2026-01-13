mtype = { // only the msgs described in the handout
    EMPTY, READY, FILLED, // over red channel (OutValveCtrl to InValveCtrl)
    STATUS_QUERY, REQ_FILLING, FILLING, // InValveCtrl over blue channel
    STATUS_QUERY_ACK, REQ_FILLING_ACK, FILLING_ACK // OutValveCtrl over blue channel
    OPEN, CLOSE // over in_cmd channel / out_cmd channel
};

// as per Listing 1
#define liquid 1; // liquid as a constant (value irrelevant)
chan Vessel = [2] of {bit}; // capacity 2 batches of liquid (tokens)

// controller to controller
chan blue = [2] of {mtype};
chan red = [2] of {mtype};

// controller to valve (synchronous / unbuffered)
chan in_cmd = [0] of {mtype}; // OPEN / CLOSE
chan out_cmd = [0] of {mtype}; // OPEN / CLOSE

proctype InValveCtrl() {

    mtype current_state;

    do
        // send status query
        :: !(blue?[STATUS_QUERY]) ->
        printf("[in controller] (blue) sent status query\n");

        // receive status query ack
        blue?STATUS_QUERY_ACK;
        printf("[in controller] (blue) received status query ack\n");

        // receive vessel state
        red?current_state;
        printf("[in controller] (red) received vessel state: %d\n");

        if // execute immediately - avoid STATUS_QUERY spam
        :: current_state == EMPTY ->
            // send filling request
            blue!REQ_FILLING;
            printf("[in controller] (blue) sent filling request\n");

            // receive filling request ack
            blue?REQ_FILLING_ACK;
            printf("[in controller] (blue) received filling request ack ack\n");

            // wait for READY
            red?READY;
            printf("[in controller] (red) received ready\n");
            current_state = READY;

            // send command OPEN to inValve
            in_cmd!OPEN;
            printf("[in controller] (outflow) sent OPEN\n");

            // notify FILLING
            blue!FILLING;
            printf("[in controller] (blue) sent filling\n");
        fi

        // Listen for FILLED
        :: red?FILLED ->
            printf("[in controller] (red) received filled\n");

            // send command CLOSE to inValve
            in_cmd!CLOSE;
            printf("[in controller] (outflow) sent CLOSE\n");   
    od
}

proctype OutValveCtrl() {

    mtype vessel_state = EMPTY;

    do // Listen for status query
    :: blue?STATUS_QUERY ->
        // send status query ack
        blue!STATUS_QUERY_ACK;
        printf("[out controller] (blue) sent status query ack\n");

        // send vessel state
        red!vessel_state;
        printf("[out controller] (red) sent vessel state: %d\n", vessel_state);

        // Listen for filling request
    :: blue?REQ_FILLING ->
        // send filling request ack
        blue!REQ_FILLING_ACK;
        printf("[out controller] (blue) sent filling request ack\n");

        // ensure outValve is closed before filling
        out_cmd!CLOSE; 
        printf("[out controller] (inflow) sent CLOSE\n");

        // send READY
        red!READY;
        printf("[out controller] (red) sent READY\n");
        vessel_state = READY;

        // Listen for FILLING
    :: blue?FILLING ->
        // send filling ack
        blue!FILLING_ACK;
        printf("[out controller] (blue) sent filling ack\n");   

        // vessel filled - send FILLED
        red!FILLED;
        printf("[out controller] (red) sent FILLED\n");
        vessel_state = FILLED;
    od

}

proctype InValve(chan outflow) {

    mtype state = CLOSE;
    mtype cmd;

    do 
    :: in_cmd?cmd -> // Listen for commands
        if 
        :: cmd == OPEN -> state = OPEN;
        :: cmd == CLOSE -> state = CLOSE;
        fi

    // Send (pour) liquid if valve is OPEN and outflow channel is not full (outflow == Vessel)
    :: state == OPEN && nfull(outflow) ->
        outflow!liquid;
        printf("InValve sent liquid\n");
    od
}

proctype OutValve(chan inflow) {

    mtype state = CLOSE;
    mtype cmd;

    do 
    :: out_cmd?cmd -> // Listen for commands
        if
        :: cmd == OPEN -> state = OPEN;
        :: cmd == CLOSE -> state = CLOSE;
        fi 

    // Receive (drain) liquid if valve is OPEN and inflow channel is not empty (inflow == Vessel)
    :: state == OPEN && nempty(inflow) ->
        inflow?liquid;
        printf("OutValve drains liquid\n");
    od
}

init {
    atomic {
        run InValveCtrl();
        run OutValveCtrl();
        run InValve(Vessel);
        run OutValve(Vessel);
    }
}

// ltl property p1 { [] <> len(Vessel) <= 2 } // Vessel never overflows
// ltl property p2 { [] <> len(Vessel) == 2 } // Vessel eventually fills up