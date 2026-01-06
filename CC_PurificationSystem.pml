mtype = {
    EMPTY, READY, FILLED,
    STATUS_QUERY, STATUS_QUERY_ACK,
    REQ_FILLING, REQ_FILLING_ACK,
    READY_ACK, FILLING, FILLING_ACK,
    OPEN, CLOSE
};

mtype vessel_state = EMPTY;

bool inValve_open = false;
bool outValve_open = false;

chan blue = [2] of {mtype};
chan red = [2] of {mtype};
chan vessel = [2] of {mtype}; // are we using it anywhere?

proctype InCtrl() {

    mtype current_state;

    do
    :: !(blue?[STATUS_QUERY]) ->
        // send status query
        blue!STATUS_QUERY;
        printf("[in controller] (blue) sent status query\n");

        // receive status query ack
        blue?STATUS_QUERY_ACK;
        printf("[in controller] (blue) received status query ack\n");

        // receive vessel state
        red?current_state;
        printf("[in controller] (red) received vessel state: %e\n", current_state);

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

            // open inValve
            inValve_open = true;
            printf("[in controller] (in valve) opened\n");

            // notify FILLING
            blue!FILLING;
            printf("[in controller] (blue) sent filling\n");

            // receive filling ack
            blue?FILLING_ACK;
            printf("[in controller] (blue) received filling ack\n");

            red?FILLED;
            printf("[in controller] (red) received FILLED\n");

            // vessel filled - update state
            current_state = FILLED;
            inValve_open = false;
            printf("[in controller] (in valve) closed\n");

        :: else ->
            // not EMPTY yet - do nothing
            skip;
        fi
    od
}

proctype OutCtrl() {

    do
        :: blue?STATUS_QUERY -> {
            // send status query ack
            blue!STATUS_QUERY_ACK;
            printf("[out controller] (blue) sent status query\n");

            // send status
            red!vessel_state;
            printf("[out controller] (red) sent status\n");
        }
        :: blue?REQ_FILLING -> {
            // send filling request ack
            blue!REQ_FILLING_ACK;
            printf("[out controller] (blue) sent filling request ack\n");

            // todo: close
            outValve_open = false;
            printf("[out controller] (out valve) closed\n");

            // send ready
            red!READY;
            printf("[out controller] (red) sent ready\n");
        }

        :: blue?FILLING -> {
            // send filling ack
            blue!FILLING_ACK;
            printf("[out controller] (blue) sent filling ack\n");

            // vessel filled - send filled
            vessel_state = FILLED;
            red!vessel_state;
            printf("[out controller] (red) sent vessel state: FILLED\n");

        }
    od
}

init {
    atomic {
        run InCtrl();
        run OutCtrl();
    }
}