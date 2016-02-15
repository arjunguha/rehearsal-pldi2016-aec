source("common.r")

df <- read.csv("../results/idempotence.csv")
df$Time <- df$Time / 1000

df <- ddply(df, c("Name"), summarise,
            Mean = mean(Time),
            Trials = length(Time),
            Sd = sd(Time),
            Se = Sd / sqrt(Trials))

plot <- ggplot(df, aes(x=Name,y=Mean)) +
  mytheme() +
  theme(legend.position = "none",
        axis.text.x=element_text(angle=50, vjust=0.5)) +
  geom_bar(stat="identity",position="dodge") +
  labs(x = "Benchmark", y = "Time (s)")
mysave("../results/idempotence.pdf", plot)
