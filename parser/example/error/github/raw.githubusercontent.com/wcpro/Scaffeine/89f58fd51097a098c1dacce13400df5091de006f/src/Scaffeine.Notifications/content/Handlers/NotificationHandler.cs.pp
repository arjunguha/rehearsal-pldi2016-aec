namespace $rootnamespace$.Handlers
{
    using Core.Interfaces.Eventing;
    using Models;
    using SignalR;

    public partial class NotificationHandler : IHandles<UserNotification>
    {
        private static object mLock = new object();
        private static NotificationHandler _instance;
        public static NotificationHandler Instance
        {
            get
            {
                if (_instance == null)
                {
                    lock (mLock)
                    {
                        _instance = new NotificationHandler();
                    }
                }
                return _instance;
            }
        }

        public void OnEvent(UserNotification e)
        {
            var context = GlobalHost.ConnectionManager.GetHubContext("notifications");
            context.Clients.notify(e);
        }
    }
}