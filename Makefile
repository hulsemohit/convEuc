CC=g++
CFLAGS=-I -Wshadow -O2 -std=c++17

all:
	$(CC) $(CFLAGS) -o out/convEuc src/*.cpp
