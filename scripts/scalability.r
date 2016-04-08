source("common.r")

df <- read.csv("../results/scalability.csv")
df$Time <- df$Time / 1000

df <- ddply(df, c("Size"), summarise,
            Mean = mean(Time),
            Trials = length(Time),
            Sd = sd(Time),
            Se = Sd / sqrt(Trials))

plot <- ggplot(df, aes(x=Size,y=Mean)) +
  mytheme() +
  theme(legend.position = "none") +
  geom_bar(stat="identity",position="dodge") +
  labs(x = "Number of conflicting resources", y = "Time (s)")
mysave("../results/scalability.pdf", plot)
