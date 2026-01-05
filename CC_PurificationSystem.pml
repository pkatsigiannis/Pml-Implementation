mtype = {
    EMPTY, READY, FILLED,
    STATUS_QUERY, STATUS_QUERY_ACK,
    REQ_FILLING, REQ_FILLING_ACK,
    READY_ACK, FILLING, FILLING_ACK,
    OPEN, CLOSE
};

mtype vessel_state = EMPTY;

bool inValve_open  = false;
bool outValve_open = false;

chan blue = [2] of {mtype};
chan red = [2] of {mtype};
chan vessel = [2] of {mtype};

active proctype InCtrl() {
    mtype current_state;
    do
    :: !(blue?[STATUS_QUERY]) ->
        blue!STATUS_QUERY;
        printf("[in controller] (blue) sent status query\n");

        blue?STATUS_QUERY_ACK;
        printf("[in controller] (blue) received status query ack\n");

        red?current_state;
        printf("[in controller] (red) received vessel state: %d\n", current_state);

        vessel_state = current_state;

    :: current_state == EMPTY ->
        blue!REQ_FILLING;
        printf("[in controller] (blue) sent filling request\n");

        blue?REQ_FILLING_ACK;
        printf("[in controller] (blue) received filling request ack ack\n");

        red?READY;
        printf("[in controller] (red) received ready\n");
        current_state = READY;
    od
}

active proctype OutCtrl() {
    do
        :: blue?eval(STATUS_QUERY) -> {
            // send status query ack
            blue!STATUS_QUERY_ACK;
            printf("[out controller] (blue) sent status query\n");

            // send status
            red!vessel_state;
            printf("[out controller] (red) sent status\n");
        }
        :: blue?eval(REQ_FILLING) -> {
            // send filling request ack
            blue!REQ_FILLING_ACK;
            printf("[out controller] (blue) sent filling request ack\n");

            // todo: close

            // send ready
            red!READY;
            printf("[out controller] (red) sent ready\n");

        }
    od
}