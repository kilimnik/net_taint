#define WIN32_LEAN_AND_MEAN /* prevent winsock.h to be included in windows.h */

#include <stdio.h>
#include <tchar.h>
#include <Windows.h>
#include <wininet.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <winsock2.h>
#include <ws2tcpip.h>


#pragma comment(lib,"ws2_32.lib")

int testWhile(char* buf) {
    int i = 0;
    while (buf!= 0)
    {
        i++;
        buf++;
    }
    return 0;
}

int test3(char* buf123) {

    int z = strlen(buf123);

    return z;
}


int* test2(char* buf123) {

    int z = strlen(buf123);

    return (int*) buf123;
}

char* test(char* buf1234) {

    int z = strlen(buf1234);

    return buf1234;
}

int main() {
    char buf123[10] = "1234";
    char* buf111 = test(buf123);
    int x = atoi(buf111);

    SOCKET s;
    struct WSAData wsa;
    
    if (WSAStartup(MAKEWORD(2, 2), &wsa) != 0)
        printf("WSAStartup failed. Error Code : %d", WSAGetLastError());

    struct sockaddr_in si_other;
    memset((char *)&si_other, 0, sizeof(si_other));
    si_other.sin_family = AF_INET;
    si_other.sin_port = htons(31337);
    si_other.sin_addr.S_un.S_addr = inet_addr("127.0.0.1");

    if ((s = socket(AF_INET, SOCK_STREAM, IPPROTO_IP)) == SOCKET_ERROR)
        printf("socket() failed with error code : %d", WSAGetLastError());

    if (connect(s, (SOCKADDR *)& si_other, sizeof(si_other)) == SOCKET_ERROR)
        printf("connect() failed with error code : %d", WSAGetLastError());

    char buf[256];
    char buf1[256];
    memset(buf, 0, sizeof(buf));

    int frecv = GetProcAddress(NULL, "recv");

    if (frecv(s, buf1, sizeof(buf1)-1, 0) == SOCKET_ERROR)
        printf("recv() failed with error code : %d", WSAGetLastError());

    if (recv(s, buf, sizeof(buf), 0) == SOCKET_ERROR)
        printf("recv() failed with error code : %d", WSAGetLastError());

    closesocket(s);

    if (buf[sizeof(buf)-1] != 0)
    {
        return;
    }
    

    char abcd[10]; 
    memcpy(abcd, buf, sizeof(buf));

    strcpy(abcd, buf);
    char* abc = buf;

    char* abc = buf[1];

    int z = strlen(buf);
    z = strlen(abcd);
    z = strlen(abc);

    int* p = (int*) test(buf);

    x = atoi(buf);
    data[x] = 0x41;

    char* retBuf = test(buf);
    x = atoi(retBuf);
    p = test2(buf);

    x = testWhile(buf);

    return 0;
}