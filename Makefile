CC=g++
CFLAGS=-O2 -std=c++17 -Wshadow

TARGET_EXEC := convEuc
BUILD_DIR := ./out
INC_DIRS := ./src
SRC_DIRS := ./src

SRCS = $(shell find $(SRC_DIRS) -name *.cpp)
DEPS = $(shell find $(INC_DIRS) -name *.h)
OBJS := $(SRCS:%=$(BUILD_DIR)/%.o)

all: $(BUILD_DIR)/$(TARGET_EXEC)

$(BUILD_DIR)/$(TARGET_EXEC): $(OBJS) $(DEPS)
	$(CC) $(OBJS) -o $@

$(BUILD_DIR)/%.cpp.o: %.cpp $(DEPS)
	mkdir -p $(dir $@)
	$(CC) $(CFLAGS) -c $< -o $@

.PHONY: generate clean
generate: $(BUILD_DIR)/$(TARGET_EXEC)
	$(BUILD_DIR)/$(TARGET_EXEC)

clean:
	rm -r $(BUILD_DIR)
