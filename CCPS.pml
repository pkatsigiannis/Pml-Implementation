mtype = {
    EMPTY, READY, FILLED, // vessel state from OutValveCtrl to InValveCtrl over red channel
    STATUS_QUERY, REQ_FILLING, FILLING, // from InValveCtrl to OutValveCtrl over blue channel
    STATUS_QUERY_ACK, REQ_FILLING_ACK, FILLING_ACK, ATTENTION, // from OutValveCtrl to InValveCtrl over blue channel
    OPEN, CLOSE // commands from controllers to valves over out_cmd and in_cmd channels
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

// from InValve to InValveCtrl
chan fromInValve = [1] of {bit};

