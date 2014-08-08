namespace $rootnamespace$.Models.Users
{
    using System.Collections.Generic;
    using Core.Model;

    public class UserActivitiesViewModel : UserViewModel
    {
        private IEnumerable<UserActivities> _activities;
        public IEnumerable<UserActivities> Activities
        {
            get { return _activities??(_activities = new List<UserActivities>()); }
            set { _activities = value; }
        }
    }
}