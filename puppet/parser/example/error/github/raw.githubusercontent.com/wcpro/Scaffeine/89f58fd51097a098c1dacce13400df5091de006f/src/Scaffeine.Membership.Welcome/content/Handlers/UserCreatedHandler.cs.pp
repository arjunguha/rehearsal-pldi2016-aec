namespace $rootnamespace$.Handlers
{
    using Core.Common.Membership.Events;
    using Core.Interfaces.Eventing;
    using Mailers;
    using Models;
    using Mvc.Mailer;

    public class UserCreatedHandler : IHandles<UserCreated>
    {
        private static UserCreatedHandler _instance;
        public static UserCreatedHandler Instance
        {
            get { return _instance ?? (_instance = new UserCreatedHandler()); }
        }

        public void OnEvent(UserCreated e)
        {
            new Mailer().WelcomeMember(new WelcomeMemberModel
            {
                Name = e.User.FirstName + " " + e.User.LastName,
                Password = e.User.Password,
                Username = e.User.Username,
                LoginUrl = e.LoginUrl,
                EmailAddress = e.User.Email
            }).Send();
        }
    }
}