mtype = { // only the msgs described in the handout
  EMPTY, READY, FILLED, // over red channel
  STATUS_QUERY, STATUS_QUERY_ACK, // over blue channel
  REQ_FILLING, REQ_FILLING_ACK, // over blue channel
  OPEN, CLOSE // over in_cmd / out_cmd channels
};

#define liquid 1; // liquid as a constant (value irrelevant)
chan Vessel = [2] of {bit}; // max capacity 2 units of liquid?

// controller to controller
chan blue = [2] of {mtype}; 
chan red  = [2] of {mtype}; 

// controller to valve (synchronous / unbuffered)
chan in_cmd  = [0] of {mtype}; // OPEN / CLOSE
chan out_cmd = [0] of {mtype};

proctype InValveCtrl() {

}

proctype OutValveCtrl() {

}

proctype InValve(chan outflow) {
    mtype state = CLOSE;
    mtype cmd;

    do
    :: // listen for commands
       in_cmd?cmd ->
        if
        :: cmd == OPEN -> state = OPEN;
        :: cmd == CLOSE -> state = CLOSE;
        fi

    :: state == OPEN && !full(outflow) ->
        outflow!liquid;
        printf("InValve sent liquid\n");
    od
}

proctype OutValve(chan inflow) {
    mtype state = CLOSE;
    mtype cmd;

    do
    :: // listen for commands
       out_cmd?cmd ->
        if
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    :: state == OPEN && !empty(inflow) ->
        inflow?liquid;
        printf("OutValve poured liquid\n")
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