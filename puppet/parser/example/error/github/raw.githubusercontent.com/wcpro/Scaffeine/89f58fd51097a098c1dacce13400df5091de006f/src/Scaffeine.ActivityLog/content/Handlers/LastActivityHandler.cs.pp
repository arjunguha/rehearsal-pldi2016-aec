namespace $rootnamespace$.Handlers
{
    using System;
    using System.Web.Mvc;
    using Core.Common.Membership.Events;
    using Core.Interfaces.Eventing;
    using Core.Interfaces.Service;
    using Core.Model;

    public class LastActivityHandler : IHandles<UserCreated>, IHandles<UserLoggedIn>, IHandles<UserLoggedOut>
    {
        private static LastActivityHandler _instance;
        public static LastActivityHandler Instance
        {
            get { return _instance ?? (_instance = new LastActivityHandler()); }
        }

        private IUserService UserService
        {
            get { return DependencyResolver.Current.GetService<IUserService>(); }
        }

        private IUserActivitiesService ActivityService
        {
            get { return DependencyResolver.Current.GetService<IUserActivitiesService>(); }
        }

        private void UpdateLastActivityDate(User user)
        {
            user.LastActivityDate = DateTime.UtcNow;
            UserService.SaveOrUpdate(user);
        }

        public void OnEvent(UserActivity e)
        {
            UpdateLastActivityDate(e.User);
            ActivityService.SaveOrUpdate(new UserActivities() {Activity = e.FriendlyName, UserId = e.User.Id});
        }

        public void OnEvent(UserCreated e)
        {
            this.OnEvent((UserActivity)e);
        }

        public void OnEvent(UserLoggedIn e)
        {
            this.OnEvent((UserActivity)e);
        }

        public void OnEvent(UserLoggedOut e)
        {
            this.OnEvent((UserActivity)e);
        }
    }
}