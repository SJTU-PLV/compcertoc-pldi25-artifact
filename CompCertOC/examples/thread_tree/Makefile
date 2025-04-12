TARGET = main
CC = ccomp
CFLAGS = -g 
LDFLAGS = -lpthread
SOURCES = $(wildcard *.c *.s)
OBJECTS = $(addprefix ,$(addsuffix .o,$(basename $(SOURCES))))

all: $(TARGET)
	@echo "Done."

$(TARGET): $(OBJECTS)
	$(CC) -o $@ $^ $(LDFLAGS) 

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.s
	$(CC) $(CFLAGS) -c $< -o $@


.PHONY: clean

clean:
	rm $(TARGET) *.o

