import Std.Time
open Std.Time

def file := ByteArray.mk <|
#[84, 90, 105, 102, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91, 0]
++ #[0, 0, 3, 0, 0, 0, 12, 150, 170, 114, 180, 184, 15, 73, 224, 184, 253, 64, 160, 185, 241, 52, 48, 186, 222, 116, 32, 218, 56, 174, 48, 218, 235, 250, 48, 220, 25]
++ #[225, 176, 220, 185, 89, 32, 221, 251, 21, 48, 222, 155, 222, 32, 223, 221, 154, 48, 224, 84, 51, 32, 244, 90, 9, 48, 245, 5, 94, 32, 246, 192, 100, 48, 247, 14, 30]
++ #[160, 248, 81, 44, 48, 248, 199, 197, 32, 250, 10, 210, 176, 250, 168, 248, 160, 251, 236, 6, 48, 252, 139, 125, 160, 29, 201, 142, 48, 30, 120, 215, 160, 31, 160, 53, 176]
++ #[32, 51, 207, 160, 33, 129, 105, 48, 34, 11, 200, 160, 35, 88, 16, 176, 35, 226, 112, 32, 37, 55, 242, 176, 37, 212, 199, 32, 39, 33, 15, 48, 39, 189, 227, 160, 41]
++ #[0, 241, 48, 41, 148, 139, 32, 42, 234, 13, 176, 43, 107, 50, 160, 44, 192, 181, 48, 45, 102, 196, 32, 46, 160, 151, 48, 47, 70, 166, 32, 48, 128, 121, 48, 49, 29]
++ #[77, 160, 50, 87, 32, 176, 51, 6, 106, 32, 52, 56, 84, 48, 52, 248, 193, 32, 54, 32, 31, 48, 54, 207, 104, 160, 55, 246, 198, 176, 56, 184, 133, 32, 57, 223, 227]
++ #[48, 58, 143, 44, 160, 59, 200, 255, 176, 60, 111, 14, 160, 61, 196, 145, 48, 62, 78, 240, 160, 63, 145, 254, 48, 64, 46, 210, 160, 65, 134, 248, 48, 66, 23, 239, 32]
++ #[67, 81, 194, 48, 67, 247, 209, 32, 69, 77, 83, 176, 69, 224, 237, 160, 71, 17, 134, 48, 71, 183, 149, 32, 72, 250, 162, 176, 73, 151, 119, 32, 74, 218, 132, 176, 75]
++ #[128, 147, 160, 76, 186, 102, 176, 77, 96, 117, 160, 78, 154, 72, 176, 79, 73, 146, 32, 80, 131, 101, 48, 81, 32, 57, 160, 82, 99, 71, 48, 83, 0, 27, 160, 84, 67]
++ #[41, 48, 84, 233, 56, 32, 86, 35, 11, 48, 86, 201, 26, 32, 88, 2, 237, 48, 88, 168, 252, 32, 89, 226, 207, 48, 90, 136, 222, 32, 91, 222, 96, 176, 92, 104, 192]
++ #[32, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]
++ #[2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]
++ #[1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 255, 255, 212, 76, 0, 0, 255, 255, 227, 224, 1, 4, 255, 255, 213, 208, 0, 8, 76]
++ #[77, 84, 0, 45, 48, 50, 0, 45, 48, 51, 0, 84, 90, 105, 102, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
++ #[0, 0, 0, 0, 0, 0, 0, 0, 0, 91, 0, 0, 0, 3, 0, 0, 0, 12, 255, 255, 255, 255, 150, 170, 114, 180, 255, 255, 255, 255, 184, 15, 73, 224, 255, 255, 255]
++ #[255, 184, 253, 64, 160, 255, 255, 255, 255, 185, 241, 52, 48, 255, 255, 255, 255, 186, 222, 116, 32, 255, 255, 255, 255, 218, 56, 174, 48, 255, 255, 255, 255, 218, 235, 250, 48]
++ #[255, 255, 255, 255, 220, 25, 225, 176, 255, 255, 255, 255, 220, 185, 89, 32, 255, 255, 255, 255, 221, 251, 21, 48, 255, 255, 255, 255, 222, 155, 222, 32, 255, 255, 255, 255, 223]
++ #[221, 154, 48, 255, 255, 255, 255, 224, 84, 51, 32, 255, 255, 255, 255, 244, 90, 9, 48, 255, 255, 255, 255, 245, 5, 94, 32, 255, 255, 255, 255, 246, 192, 100, 48, 255, 255]
++ #[255, 255, 247, 14, 30, 160, 255, 255, 255, 255, 248, 81, 44, 48, 255, 255, 255, 255, 248, 199, 197, 32, 255, 255, 255, 255, 250, 10, 210, 176, 255, 255, 255, 255, 250, 168, 248]
++ #[160, 255, 255, 255, 255, 251, 236, 6, 48, 255, 255, 255, 255, 252, 139, 125, 160, 0, 0, 0, 0, 29, 201, 142, 48, 0, 0, 0, 0, 30, 120, 215, 160, 0, 0, 0, 0]
++ #[31, 160, 53, 176, 0, 0, 0, 0, 32, 51, 207, 160, 0, 0, 0, 0, 33, 129, 105, 48, 0, 0, 0, 0, 34, 11, 200, 160, 0, 0, 0, 0, 35, 88, 16, 176, 0]
++ #[0, 0, 0, 35, 226, 112, 32, 0, 0, 0, 0, 37, 55, 242, 176, 0, 0, 0, 0, 37, 212, 199, 32, 0, 0, 0, 0, 39, 33, 15, 48, 0, 0, 0, 0, 39, 189]
++ #[227, 160, 0, 0, 0, 0, 41, 0, 241, 48, 0, 0, 0, 0, 41, 148, 139, 32, 0, 0, 0, 0, 42, 234, 13, 176, 0, 0, 0, 0, 43, 107, 50, 160, 0, 0, 0]
++ #[0, 44, 192, 181, 48, 0, 0, 0, 0, 45, 102, 196, 32, 0, 0, 0, 0, 46, 160, 151, 48, 0, 0, 0, 0, 47, 70, 166, 32, 0, 0, 0, 0, 48, 128, 121, 48]
++ #[0, 0, 0, 0, 49, 29, 77, 160, 0, 0, 0, 0, 50, 87, 32, 176, 0, 0, 0, 0, 51, 6, 106, 32, 0, 0, 0, 0, 52, 56, 84, 48, 0, 0, 0, 0, 52]
++ #[248, 193, 32, 0, 0, 0, 0, 54, 32, 31, 48, 0, 0, 0, 0, 54, 207, 104, 160, 0, 0, 0, 0, 55, 246, 198, 176, 0, 0, 0, 0, 56, 184, 133, 32, 0, 0]
++ #[0, 0, 57, 223, 227, 48, 0, 0, 0, 0, 58, 143, 44, 160, 0, 0, 0, 0, 59, 200, 255, 176, 0, 0, 0, 0, 60, 111, 14, 160, 0, 0, 0, 0, 61, 196, 145]
++ #[48, 0, 0, 0, 0, 62, 78, 240, 160, 0, 0, 0, 0, 63, 145, 254, 48, 0, 0, 0, 0, 64, 46, 210, 160, 0, 0, 0, 0, 65, 134, 248, 48, 0, 0, 0, 0]
++ #[66, 23, 239, 32, 0, 0, 0, 0, 67, 81, 194, 48, 0, 0, 0, 0, 67, 247, 209, 32, 0, 0, 0, 0, 69, 77, 83, 176, 0, 0, 0, 0, 69, 224, 237, 160, 0]
++ #[0, 0, 0, 71, 17, 134, 48, 0, 0, 0, 0, 71, 183, 149, 32, 0, 0, 0, 0, 72, 250, 162, 176, 0, 0, 0, 0, 73, 151, 119, 32, 0, 0, 0, 0, 74, 218]
++ #[132, 176, 0, 0, 0, 0, 75, 128, 147, 160, 0, 0, 0, 0, 76, 186, 102, 176, 0, 0, 0, 0, 77, 96, 117, 160, 0, 0, 0, 0, 78, 154, 72, 176, 0, 0, 0]
++ #[0, 79, 73, 146, 32, 0, 0, 0, 0, 80, 131, 101, 48, 0, 0, 0, 0, 81, 32, 57, 160, 0, 0, 0, 0, 82, 99, 71, 48, 0, 0, 0, 0, 83, 0, 27, 160]
++ #[0, 0, 0, 0, 84, 67, 41, 48, 0, 0, 0, 0, 84, 233, 56, 32, 0, 0, 0, 0, 86, 35, 11, 48, 0, 0, 0, 0, 86, 201, 26, 32, 0, 0, 0, 0, 88]
++ #[2, 237, 48, 0, 0, 0, 0, 88, 168, 252, 32, 0, 0, 0, 0, 89, 226, 207, 48, 0, 0, 0, 0, 90, 136, 222, 32, 0, 0, 0, 0, 91, 222, 96, 176, 0, 0]
++ #[0, 0, 92, 104, 192, 32, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]
++ #[1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]
++ #[2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 255, 255, 212, 76, 0, 0, 255, 255, 227, 224, 1, 4, 255, 255]
++ #[213, 208, 0, 8, 76, 77, 84, 0, 45, 48, 50, 0, 45, 48, 51, 0, 10, 60, 45, 48, 51, 62, 51, 10]

def code := Std.Time.TimeZone.TZif.parse.run file |>.toOption |>.get!

def rules :=
  match TimeZone.convertTZif code "America/Sao_Paulo" with
  | .ok res => res
  | .error err => panic! err

/--
info: { version := 50, isutcnt := 0, isstdcnt := 0, leapcnt := 0, timecnt := 91, typecnt := 3, charcnt := 12 }
-/
#guard_msgs in
#eval code.v1.header

/--
info: 0
-/
#guard_msgs in
#eval code.v1.leapSeconds.size

/--
info: 3
-/
#guard_msgs in
#eval code.v1.abbreviations.size

/--
info: 91
-/
#guard_msgs in
#eval code.v1.transitionIndices.size

/--
info: 91
-/
#guard_msgs in
#eval code.v1.transitionTimes.size

/--
info: 3
-/
#guard_msgs in
#eval code.v1.localTimeTypes.size

/--
info: 0
-/
#guard_msgs in
#eval code.v1.stdWallIndicators.size

/--
info: 0
-/
#guard_msgs in
#eval code.v1.utLocalIndicators.size

/--
info: zoned("1969-12-31T21:00:00.000000000-03:00")
-/
#guard_msgs in
#eval ZonedDateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 0) rules

/--
info: zoned("2012-12-10T00:35:47.000000000-02:00")
-/
#guard_msgs in
#eval ZonedDateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 1355106947) rules
