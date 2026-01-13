mtype = { // only the msgs described in the handout
    EMPTY, READY, FILLED, // over red channel (OutValveCtrl to InValveCtrl)
    STATUS_QUERY, STATUS_QUERY_ACK, // over blue channel
    REQ_FILLING, REQ_FILLING_ACK, // over blue channel
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
    od
}

proctype OutValveCtrl() {

    do // Listen for status query
    :: blue?STATUS_QUERY ->
        // send status query ack
        blue!STATUS_QUERY_ACK;
        printf("[out controller] (blue) sent status query ack\n");

        // ;
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
    :: state == OPEN && !full(outflow) ->
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
    :: state == OPEN && !empty(inflow) ->
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
