gcc -O3 yoctoLisp.c -o yoctolisp -lm
# --- verifica della memoria con memwatch ---
#gcc -O3 -DDEBUG_C_MEMORY yoctoLisp.c memwatch.c -o yoctolisp -lm
# --- compilazione per valgrind ---
#gcc -g -O0 yoctoLisp.c -o yoctolisp -lm
