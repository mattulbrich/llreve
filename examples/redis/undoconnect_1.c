#include "server.h"

int slaveIsInHandshakeState(void) {
    return (server.repl_state >= REPL_STATE_RECEIVE_PONG &&
            server.repl_state <= REPL_STATE_RECEIVE_PSYNC) ? 1 : 0;
}

void undoConnectWithMaster(void) {
    int fd = server.repl_transfer_s;

    serverAssert(server.repl_state == REPL_STATE_CONNECTING ||
                server.repl_state == REPL_STATE_RECEIVE_PONG);
    aeDeleteFileEvent(server.el,fd,AE_READABLE|AE_WRITABLE);
    close(fd);
    server.repl_transfer_s = -1;
    server.repl_state = REPL_STATE_CONNECT;
}
