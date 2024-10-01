#include <stdio.h>
#include <wchar.h>
#include <locale.h>

int main(int argc, char** argv) {
  int c = 161;
  setlocale(LC_ALL, "");
  int written = wprintf(L"U+%04X = '%lc'\n", c, (wchar_t)c);
  if (written < 0)
      perror(argv[0]);
  return 0;
}
