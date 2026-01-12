mtype = { // Only the msgs described in the handout
    EMPTY, READY, FILLED, // Over red channel
    STATUS_QUERY, STATUS_QUERY_ACK, // Over blue channel
    REQ_FILLING, REQ_FILLING_ACK, // Over blue channel
    OPEN, CLOSE // Over in_cmd channel / out_cmd channel
};

// As per Listing 1
#define liquid 1; // liquid as a constant (value irrelevant)
chan Vessel = [2] of {bit}; // max capacity 2 units of liquid?

// Controller to controller
chan blue = [2] of {mtype};
chan red = [2] of {mtype};

// Controller to valve (synchronous / unbuffered)
chan in_cmd = [0] of {mtype}; // OPEN / CLOSE
chan out_cmd = [0] of {mtype}; // OPEN / CLOSE

proctype InValveCtrl() {

}

proctype OutValveCtrl() {

}

proctype InValve(chan outflow) {
    mtype state = CLOSE;
    mtype cmd;

    do 
    :: // Listen for commands
        in_cmd?cmd ->
        if 
        :: cmd == OPEN -> state = OPEN;
        :: cmd == CLOSE -> state = CLOSE;
        fi

    :: // If command is OPEN, send liquid
        outflow!liquid;
        printf("InValve sent liquid\n");
    od
}

proctype OutValve(chan inflow) {
    mtype state = CLOSE;
    mtype cmd;

    do 
    :: // Listen for commands
        out_cmd?cmd ->
        if
        :: cmd == OPEN -> state = OPEN;
        :: cmd == CLOSE -> state = CLOSE;
        fi 

    // If command is OPEN, receive liquid (drain Vessel)
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
