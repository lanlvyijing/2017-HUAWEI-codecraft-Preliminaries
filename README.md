# 2017-HUAWEI-codecraft-Preliminaries
using Special optimization SPFA algorithm. 19th of the preliminary round .

The algorithm is divided into two stages
1.Greedy Approach：all the operation in this stage is to turn one station into a normal point in one turn. To find which one is the best to turn, you should try turn every station, if the total cost is declining ,then record the cost and the point.You should recover every station you have changed. After all the station have tried to change,change the one that make the total cost minimum, and start a new turn.
In particular，when turning a station into a normal point,there's no need to do a Cost flow algorithm for all the flow that the custom need, you just do it for flow provided by the station which has turned into normal point.This is the special trick to speed up the algorithm

2.Random method：Use the following actions to reduce the overall cost and keep the change
   1）Randomly selected a station to turn into normal point. 
   2）Randomly selected a normal point to turn into station. 
   3）Randomly selected a station and swap with its neighbor point. 
