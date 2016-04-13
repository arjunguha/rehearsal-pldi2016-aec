source("common.r")

# df %>% mutate(Type = paste(Pruning, Commutativity)) %>% select(-Pruning, -Commutativity)

df <- read.csv("../results/determinism.csv")
df$Time <- df$Time / 1000
df <- df
  %>% filter(Commutativity = " true")
  %>% select(-Commutativity)
  %>% transform(Pruning = gsub("no-pruning", "No", Pruning))
  %>% transform(Pruning = gsub("pruning", "Yes", Pruning))
df <- ddply(df, c("Name", "Pruning"), summarise,
            Mean = mean(Time),
            Trials = length(Time),
            Sd = sd(Time),
            Se = Sd / sqrt(Trials))

plot <- ggplot(df, aes(x=Name,y=Mean,fill=Pruning)) +
  mytheme() +
  theme(legend.title = element_text(size = 8),
        legend.position = c(0.85, 0.8),
        axis.text.x=element_text(angle=50, vjust=0.5)) +
  geom_bar(stat="identity",position="dodge") +
  labs(x = "Benchmark", y = "Time (s)")
mysave("../results/determinism.pdf", plot)
